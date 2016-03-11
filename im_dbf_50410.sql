CREATE OR REPLACE PACKAGE  "IM_DBF" as
/*
  IMport DBF/MEMO table from BLOB
  2015 miktim@mail.ru, Petrozavodsk State University: https://petrsu.ru/en
  2015.04.17 memo support added
  2015.04.10 conversion functions p_endian added
  2015.04.09 tableCREATE
  2015.04.08
*/
-- ***Open/close dbf file
default_charset constant varchar2(16) := 'RU8PC866';
Procedure dbUSE
( p_dbfblob BLOB
, p_charset varchar2 := default_charset ); -- Notes:
-- 1. procedure doesn't check: is it really dbf-file
-- 2. only one dbf can be used
Procedure dbCLOSE;
-- ***Structure
Type tp_field is record
( name varchar2(10)
, type char(1)
, len pls_integer
, dec pls_integer
);
Type tp_struct is table of tp_field;
Function dbSTRUCT return tp_struct;
Function LUPDATE return date;
Function SUPPORTED
( nFieldPos pls_integer 
) return boolean; -- True, if dbf field type supported by package (C,N,D,L,M)
-- ***Positioning
Function RECCOUNT return pls_integer; -- record count from dbf header
Function RECNO return pls_integer;    -- current record number
Procedure dbGOTO ( nRecordNumber pls_integer );
Procedure SKIP ( nRecords pls_integer := 1 ); 
Function DELETED return boolean; -- True, if current record is marked as deleted
-- ***Fields & values
Function fieldNAME( nFieldPos pls_integer ) return varchar2;
Function fieldPOS( cFieldName varchar2) return pls_integer;
Function fieldRAW -- current record used
( nFieldPos pls_integer 
) return raw;
Function fieldGET -- current record used
( nFieldPos pls_integer 
) return varchar2; -- Notes:
-- 1. returned Date and Number strings can be implicitly converted to appropriate type
-- 2. returned Char strings is right-trimmed
-- 3. MEMO return number of block
-- 4. for unsupported field types rawtohex() string returned
Procedure memoGET(p_blob in out nocopy BLOB, p_memoblob in BLOB, nFieldPos pls_integer);
Procedure memoGET(p_clob in out nocopy CLOB, p_memoblob in BLOB, nFieldPos pls_integer);
-- ***Searching for...
Type tp_field_val is record
( nRecNo number(10)
, cValue varchar2(1000)
);
Type tp_values_tbl is table of tp_field_val;
Function valuesTBL
( nFieldPos pls_integer
, cShowDeleted char := 'Y' 
) return tp_values_tbl pipelined;
-- ***Import
Procedure tableCREATE
( p_tablename varchar2 -- Oracle table name 
, p_struct tp_struct := tp_struct()); -- Notes:
-- 1. C - varchar2, N - number, D - date, L - char(1), M - number(10,0)
-- 2. for unsupported types varchar2(<dbf_field>.len*2) columns created
-- 3. for Oracle UTF charsets set correct C-type field length: *2, *3,...
Type tp_record is table of varchar2(1000);
Function recordGET
( nRecordNumber pls_integer := null -- if null, current record used 
) return tp_record;   
Procedure recordADD
( p_tablename varchar2 -- Oracle table name
, p_record tp_record
, p_columns varchar2 := ''); -- Notes:
-- 1. record values associate with table columns in column_id order
-- 2. association order can be changed using comma-delimited column list 
-- 3. column name in the column list can be omitted
-- ***Decoding (packing order of bytes is important!)
Function longInt2number
( p_raw raw
, p_endian pls_integer := utl_raw.little_endian
) return number;
Function julianDays2date
( p_raw raw
, p_endian pls_integer := utl_raw.big_endian
) return date;
Function radix502varchar
( p_raw raw
, p_endian pls_integer := utl_raw.big_endian
) return varchar2;
end;
/
CREATE OR REPLACE PACKAGE BODY  "IM_DBF" is
hdr_rec_len constant pls_integer := 32;
nls_dec_sep char(1);
Type tp_header is record
( updated date
, rec_cnt pls_integer -- 4-7 (start from 0!)
, hdr_len pls_integer -- 8-9
, rec_len pls_integer -- 10-11
, lang_id pls_integer -- 29
);
Type tp_fnames is table of pls_integer index by varchar2(10);
Type tp_offset is table of pls_integer index by pls_integer;
Type tp_dbf is record
( file BLOB
, charset varchar2(16)
, header tp_header
, struct tp_struct:=tp_struct()
, fields tp_fnames
, offset tp_offset
, rec_no pls_integer
, rec_raw raw(32000)
);
--
dbf tp_dbf;
--
Type tp_memo_ref is record
( prefix pls_integer
, length pls_integer
, blockn pls_integer
);
--
Function get_integer( p_blob blob, p_len integer, p_pos integer )
return number
is
begin
  return utl_raw.cast_to_binary_integer( dbms_lob.substr( p_blob, p_len, p_pos ), utl_raw.little_endian );
end;
--
Function get_memoref( p_raw raw) return tp_memo_ref
is
l_mref tp_memo_ref;
l_space constant raw(1) := hextoraw('40');
begin
  if utl_raw.substr(p_raw,1,1) = l_space then -- space padded? - .dbt style
    l_mref.blockn := trim(utl_raw.cast_to_varchar2(p_raw)); 
  else -- .smt style
    l_mref.prefix := utl_raw.cast_to_binary_integer(
      utl_raw.substr(p_raw,1,2),utl_raw.little_endian);
    l_mref.length := utl_raw.cast_to_binary_integer(
      utl_raw.substr(p_raw,3,4),utl_raw.little_endian);
    l_mref.blockn := utl_raw.cast_to_binary_integer(
      utl_raw.substr(p_raw,7,4),utl_raw.little_endian);
  end if;
  return l_mref;
end;
--
Function raw2varchar2( p_raw raw, p_encoding varchar2 := dbf.charset )
return varchar2
is
begin
  return utl_i18n.raw_to_char( p_raw, p_encoding );
end;
--
Function get_string0( p_blob blob, p_len integer, p_pos integer, p_encoding varchar2 := null  )
return varchar2
is
  l_raw raw(4000);
  l_len pls_integer;
begin
  l_raw := dbms_lob.substr( p_blob, p_len, p_pos ); 
  l_len := dbms_lob.instr( l_raw, utl_raw.cast_to_raw( chr(0) ) )-1;
  if l_len < 1 then return raw2varchar2(l_raw, p_encoding); end if;
  return raw2varchar2(utl_raw.substr(l_raw, 1, l_len), p_encoding);
end;
--
Function get_string( p_blob blob, p_len integer, p_pos integer, p_encoding varchar2 := null )
return varchar2
is
begin
  return raw2varchar2( dbms_lob.substr( p_blob, p_len, p_pos), null );
end;
--
Procedure dbCLOSE
as
  l_nullhd tp_header;
begin
  if dbms_lob.istemporary(dbf.file) = 1 
    then dbms_lob.freetemporary(dbf.file);
  end if;
  dbf.fields.delete();
  dbf.struct.delete();
  dbf.offset.delete();
  dbf.rec_raw := hextoraw('');
  dbf.header := l_nullhd;
  dbf.rec_no := 0;
end;
--
Function get_record(p_dbf blob, p_recno pls_integer) return blob
is
begin
  return dbms_lob.substr(p_dbf, dbf.header.rec_len
      , dbf.header.hdr_len + ( ( p_recno - 1 ) * dbf.header.rec_len ) + 1 );
end;
--
Procedure dbGOTO ( nRecordNumber pls_integer )
as
begin
  if nRecordNumber > dbf.header.rec_cnt then
    dbf.rec_no := dbf.header.rec_cnt + 1;
    dbf.rec_raw := utl_raw.cast_to_raw(rpad('', dbf.header.rec_len, chr(0)));
  else
    dbf.rec_no := case when nRecordNumber < 1 then 1 else nRecordNumber end;
    dbf.rec_raw := get_record( dbf.file, dbf.rec_no );
  end if;
end;
-- 
Procedure SKIP ( nRecords pls_integer := 1 )
as
begin
  dbGoTo( dbf.rec_no + nRecords );
end;
--
Procedure set_header
( p_dbf blob
)
as
l_uyear pls_integer;
begin
  l_uyear := get_integer(p_dbf,1,2);
  l_uyear := l_uyear + case when l_uyear < 80 then 2000 else 1900 end;
  dbf.header.updated := to_date(l_uyear
    ||to_char(get_integer(p_dbf,1,3),'00')||to_char(get_integer(p_dbf,1,4),'00')
    ,'YYYY MM DD');
  dbf.header.rec_cnt := get_integer(p_dbf, 4, 5);
  dbf.header.hdr_len := get_integer(p_dbf, 2, 9);
  dbf.header.rec_len := get_integer(p_dbf, 2, 11);
  dbf.header.lang_id := get_integer(p_dbf, 1, 30);
--dbms_output.put_line(dbf.header.rec_cnt||'|'||dbf.header.hdr_len
--    ||'|'||dbf.header.rec_len||'|'||dbf.header.lang_id); 
  for i in 1..floor(dbf.header.hdr_len/hdr_rec_len)-1 loop
    dbf.struct.extend();
    dbf.struct(i).name := upper(trim(get_string0(p_dbf, 11, i*hdr_rec_len+1)));
    dbf.struct(i).type := get_string(p_dbf, 1, i*hdr_rec_len+12);
    dbf.struct(i).len := get_integer(p_dbf, 1, i*hdr_rec_len+17);
    dbf.struct(i).dec := get_integer(p_dbf, 1, i*hdr_rec_len+18);
    dbf.fields(dbf.struct(i).name) := i;  
    dbf.offset(i) := case when i = 1 then 2 
        else dbf.offset(i-1) + dbf.struct(i-1).len end;
--dbms_output.put_line(i||'|'||dbf.struct(i).name||'|'||dbf.struct(i).type
--    ||'|'||dbf.struct(i).len||'.'||dbf.struct(i).dec); 
  end loop;
end;
--
Procedure dbUSE
( p_dbfblob BLOB
, p_charset varchar2 := default_charset 
)
as
begin
  dbCLOSE;
  dbf.charset := p_charset;
  set_header(p_dbfblob);
  dbf.file := p_dbfblob;
  dbf.rec_no := 0;
  dbGOTO(1);
end;
--
Function LUPDATE return date
is
begin
  return dbf.header.updated;
end;
--
Function dbSTRUCT return tp_struct
is
begin
  return dbf.struct;
end;
--
Function SUPPORTED( nFieldPos pls_integer ) return boolean
is
begin
  return dbf.struct(nFieldPos).type in ('CDNLM');
end;
--
Function RECCOUNT return pls_integer
is
begin
  return dbf.header.rec_cnt;
end;
--
Function RECNO return pls_integer
is
begin
  return dbf.rec_no;
end;
--
Function DELETED
return boolean
is
begin
  return utl_raw.cast_to_varchar2(utl_raw.substr(dbf.rec_raw,1,1)) = '*';  
end;
--
Function fieldNAME(nFieldPos pls_integer) return varchar2
is
begin
  return dbf.struct(nFieldPos).name;
exception when others then return '';
end;
---
Function fieldPOS(cFieldName varchar2) return pls_integer
is
begin
  return dbf.fields(upper(trim(cFieldName)));
exception when others then return 0;
end;
--
Function fieldRAW(nFieldPos pls_integer) return raw
is
begin
  return utl_raw.substr(dbf.rec_raw, dbf.offset(nFieldPos), dbf.struct(nFieldpos).len);
end;
--
Function fieldGET( nFieldPos pls_integer ) return varchar2
is 
begin
  case dbf.struct(nFieldPos).type
    when 'C' then return rtrim(raw2varchar2(fieldRAW(nFieldPos)));
    when 'D' then return to_date(utl_raw.cast_to_varchar2(fieldRAW(nFieldPos)),'YYYYMMDD'); 
    when 'N' then return 
      replace(replace(utl_raw.cast_to_varchar2(fieldRAW(nFieldPos)),' ',''),'.',nls_dec_sep);
    when 'M' then return get_memoref(fieldRAW(nFieldPos)).blockn;
    when 'L' then return raw2varchar2(fieldRAW(nFieldPos));
    else return rawtohex(fieldRAW(nFieldPos));
  end case;
exception when others then return null;
end;
--
Procedure memoGET(p_blob in out nocopy BLOB, p_memoblob in BLOB, nFieldPos pls_integer)
as
l_mref tp_memo_ref;
l_blksz pls_integer;
l_moff pls_integer;
l_mlen pls_integer;
begin
  dbms_lob.createtemporary(p_blob, TRUE, dbms_lob.session);
  if dbf.struct(nFieldPos).type <> 'M' then
    p_blob := null;
  else
    l_blksz:= get_integer(p_memoblob, 4, 5);
    l_mref := get_memoref(fieldRAW(nFieldPos));
    l_moff := (l_blksz * l_mref.blockn) + 1;
    l_mlen := l_blksz * l_mref.length;
    if l_mlen is null then -- .dbt style 
        null;
    end if;
-- dbms_output.put_line(l_mref.blockn||'|'||l_mref.length||'|'||l_blksz);
    dbms_lob.copy(p_blob, p_memoblob, l_mlen, 1, l_moff);
  end if;
end;
--
Procedure blob2clob(p_clob in out nocopy CLOB, p_blob in BLOB, p_charset varchar2:=null)
as
  c_lob_maxsize number := DBMS_LOB.LOBMAXSIZE;
  c_lang_context  integer := DBMS_LOB.DEFAULT_LANG_CTX;
  c_warning       integer := DBMS_LOB.WARN_INCONVERTIBLE_CHAR;
  c_start_blob number := 1;
  c_start_clob number := 1;
begin
--  dbms_lob.createtemporary(p_clob, TRUE, dbms_lob.session);
  DBMS_LOB.CONVERTTOCLOB
  ( dest_lob    =>p_clob
  , src_blob    =>p_blob
  , amount      =>c_lob_maxsize
  , dest_offset =>c_start_clob
  , src_offset  =>c_start_blob
  , blob_csid   =>NLS_CHARSET_ID (nvl(dbf.charset,default_charset))
  , lang_context=>c_lang_context
  , warning     =>c_warning
  );
end;
--
Procedure memoGET(p_clob in out nocopy CLOB, p_memoblob in BLOB, nFieldPos pls_integer)
as
l_blob BLOB;
begin
--  dbms_lob.createtemporary(p_clob, TRUE, dbms_lob.session);
  memoGET(l_blob, p_memoblob, nFieldPos);
  blob2clob(p_clob, l_blob, dbf.charset);
  if dbms_lob.istemporary(l_blob)=1 then dbms_lob.freetemporary(l_blob); end if;
end;
--
Function valuesTBL
( nFieldPos pls_integer
, cShowDeleted char := 'Y' 
) return tp_values_tbl pipelined
is
  l_val tp_field_val;    
begin
 for i in 1..dbf.header.rec_cnt loop
   dbGOTO(i);
   continue when deleted() and upper(cShowDeleted) <> 'Y';
   l_val.nRecNo := i;
   l_val.cValue := fieldGET( nFieldPos );
   pipe row(l_val);
 end loop;
 return;
end;
--
Procedure tableCREATE(p_tablename varchar2, p_struct tp_struct := tp_struct())
as
  l_exec varchar2(4000);
  l_struct tp_struct;
begin
  l_struct := p_struct;
  if l_struct.count() = 0 then l_struct := dbSTRUCT(); end if;
  if l_struct.count() = 0 then return; end if;
  
  l_exec := 'CREATE TABLE "'||replace(upper(p_tablename),'.','_')||'" ';
  for i in 1..l_struct.last() loop
    l_exec := l_exec || '
'|| case when i = 1 then '( "' else ', "' end || l_struct(i).name || '" ' ||
    case l_struct(i).type 
      when 'D' then ' DATE '
      when 'N' then ' NUMBER('|| l_struct(i).len || ',' ||l_struct(i).dec || ') '
      when 'M' then ' NUMBER('|| l_struct(i).len || ',' ||l_struct(i).dec || ') '
      when 'L' then ' CHAR(1) '
      when 'C' then ' VARCHAR2(' || l_struct(i).len || ') '
      else ' VARCHAR2(' || l_struct(i).len*2 || ') '
    end;
  end loop;
  l_exec := l_exec||'
)';
--dbms_output.put_line(l_exec);
  execute immediate l_exec; 
  l_struct.delete();
end;    
--
Function recordGET
( nRecordNumber pls_integer := null
) return tp_record
is
  l_record tp_record:=tp_record();
begin
  if nRecordNumber is not null then dbGOTO(nRecordNumber); end if;
  for i in 1..dbf.struct.count() loop
    l_record.extend();
    l_record(i) := fieldGET(i);
  end loop;
  return l_record;
end;
--
Procedure recordADD
( p_tablename varchar2
, p_record tp_record 
, p_columns varchar2 := '')
as
  l_tablename varchar2(100):= replace(upper(p_tablename),'.','_');
  l_columnlist varchar2(4000) := p_columns;
  l_names APEX_APPLICATION_GLOBAL.VC_ARR2; 
  l_valuelist varchar2(4000);
begin
  if p_columns is null then
    select listagg(column_name,',') within group (order by column_id)
      into l_columnlist
      from user_tab_columns
      where upper(table_name) = upper(l_tablename);
--      order by column_id;
  end if;
  l_names := APEX_UTIL.STRING_TO_TABLE(l_columnlist,',');
  l_columnlist := '';
  for i in 1..least(p_record.count(),l_names.count()) loop
    continue when trim(l_names(i)) is null;
    l_columnlist:=l_columnlist||
      case when l_columnlist is null then '' else ',' end ||
      trim(l_names(i)) ;
    l_valuelist:=l_valuelist||
      case when l_valuelist is null then '''' else ',''' end || 
      replace(p_record(i),'''','''''') || '''';
  end loop;
--dbms_output.put_line('insert into '||l_tablename||' ('||l_fieldlist||') values ('||l_valuelist||')');
  execute immediate 
    'insert into '||l_tablename||' ('||l_columnlist||') values ('||l_valuelist||')';
end;
-- 4 byte raw julian days to date
Function julianDays2date
( p_raw raw
, p_endian pls_integer := utl_raw.big_endian
) return date
is
begin
  return to_date(
    utl_raw.cast_to_binary_integer(utl_raw.substr(p_raw,1,4), p_endian)
   , 'J');
end;
-- 4 byte raw int to number
Function longInt2number
( p_raw raw
, p_endian pls_integer := utl_raw.little_endian
) return number
is
begin
    return utl_raw.cast_to_binary_integer(utl_raw.substr(p_raw,1,least(utl_raw.length(p_raw),4)),p_endian);
end;
-- radix50 raw string to varchar2
Function radix502varchar
( p_raw raw
, p_endian pls_integer := utl_raw.big_endian
) return varchar2
is
  c_r50tbl constant char(40) := ' ABCDEFGHIJKLMNOPQRSTUVWXYZ$.?0123456789';
  l_str varchar2(4000);
  l_i16 pls_integer;
begin
  for i in 0..(utl_raw.length(p_raw)-2)/2 loop
    l_i16 := utl_raw.cast_to_binary_integer(
          utl_raw.substr( p_raw || hextoraw('00'), i*2+1, 2)
        , p_endian); 
    l_str := l_str || 
       substr(c_r50tbl, floor(l_i16 / 1600) + 1, 1) || -- *1600
       substr(c_r50tbl, mod(floor(l_i16 / 40), 40) + 1, 1) || -- *40
       substr(c_r50tbl, mod(l_i16, 40) + 1, 1); 
  end loop;
  return l_str;
end;
-- init package
begin
  select substr(value, 1, 1) into nls_dec_sep from nls_session_parameters
    where parameter='NLS_NUMERIC_CHARACTERS';
end;
/

