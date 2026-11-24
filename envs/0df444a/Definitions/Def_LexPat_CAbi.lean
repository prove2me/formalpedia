-- Prove2me | Definitions.Def_LexPat_CAbi
-- name    : LexPat_CAbi
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:16:49.415829+00:00
-- url     : https://prove2.me/theorems/b7703724-9ea4-48d4-9375-3c3c21c1c557
-- title:
--   CAbi
-- statement:
--   Definitions and structural lemmas for CAbi, from scidonia/lexpat contributors (see pinned LICENSE and source headers)'s pinned UTF-8 decoder properties for LexPat development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scidonia/lexpat/blob/15eee92b433940e5481f09c7f77e6f833e5f684d/LexPat/CAbi.lean

import Definitions.Def_LexPat_Stream
set_option autoImplicit true
namespace LexPat.CAbi
opaque emitXmlDecl (version : String) (encoding : String) (hasEncoding : UInt8)
  (standalone : Int64) (byteOffset line column : UInt64) : UInt64 := 0
opaque emitStart (name : String) (attrs : Array (String × String))
  (byteOffset line column : UInt64) : UInt64 := 0
opaque emitStartSlice (owner : ByteArray) (nameStart nameStop base : UInt64)
  (ranges : Array UInt64) (byteOffset line column : UInt64) : UInt64 := 0
opaque emitEnd (name : String) (byteOffset line column : UInt64) : UInt64 := 0
opaque emitEndSlice (owner : ByteArray) (nameStart nameStop base : UInt64)
  (byteOffset line column : UInt64) : UInt64 := 0
opaque emitText (owner : ByteArray) (start stop base : UInt64)
  (byteOffset line column : UInt64) : UInt64 := 0
opaque emitTextString (data : String) (byteOffset line column : UInt64) : UInt64 := 0
opaque emitTextBytes (data : ByteArray) (byteOffset line column : UInt64) : UInt64 := 0
opaque emitCdataStart (byteOffset line column : UInt64) : UInt64 := 0
opaque emitCdataEnd (byteOffset line column : UInt64) : UInt64 := 0
opaque emitComment (data : String) (byteOffset line column : UInt64) : UInt64 := 0
opaque emitPi (target : String) (data : String) (byteOffset line column : UInt64) :
  UInt64 := 0
opaque reportStatus (status code offset line column rawConsumed : UInt64) : UInt64 := 0
def standaloneValue : Option Bool → Int64
  | none => -1
  | some false => 0
  | some true => 1
def emit (base : Nat) (owner : ByteArray) (e : LocatedEvent) : Bool :=
  let off := UInt64.ofNat e.byteOffset
  let line := UInt64.ofNat e.line
  let col := UInt64.ofNat e.column
  match e.event with
  | .text data =>
    match e.textSpan, e.textBytes with
    | some sp, _ =>
      emitText owner (UInt64.ofNat sp.start) (UInt64.ofNat sp.stop)
        (UInt64.ofNat base) off line col == 0
    | none, some bytes => emitTextBytes bytes off line col == 0
    | none, none => emitTextString data off line col == 0
  | .start name attrs =>
    match e.nameSpan, e.attrRanges with
    | some sp, some ranges =>
      emitStartSlice owner (UInt64.ofNat sp.start) (UInt64.ofNat sp.stop)
        (UInt64.ofNat e.sliceBase) ranges off line col == 0
    | _, _ => emitStart name attrs off line col == 0
  | .end name =>
    match e.nameSpan with
    | some sp =>
      emitEndSlice owner (UInt64.ofNat sp.start) (UInt64.ofNat sp.stop)
        (UInt64.ofNat e.sliceBase) off line col == 0
    | none => emitEnd name off line col == 0
  | .comment data => emitComment data off line col == 0
  | .pi target data => emitPi target data off line col == 0
  | .cdataStart => emitCdataStart off line col == 0
  | .cdataEnd => emitCdataEnd off line col == 0
  | .xmlDecl version encoding standalone =>
    match encoding with
    | some enc => emitXmlDecl version enc 1 (standaloneValue standalone) off line col == 0
    | none => emitXmlDecl version "" 0 (standaloneValue standalone) off line col == 0
def statusCode (s : Stream) : UInt64 :=
  match s.status with
  | .active => 0
  | .done => 1
  | .failed _ => 2
def errorIndex : ErrorCode → UInt64
  | .syntaxErr => 0
  | .noElements => 1
  | .invalidToken => 2
  | .unclosedToken => 3
  | .partialChar => 4
  | .tagMismatch => 5
  | .duplicateAttribute => 6
  | .junkAfterDocElement => 7
  | .undefinedEntity => 8
  | .badCharRef => 9
  | .misplacedXmlPi => 10
  | .unknownEncoding => 11
  | .incorrectEncoding => 12
  | .unclosedCdataSection => 13
  | .xmlDecl => 14
  | .unsupportedDtd => 15
  | .limitInput => 16
  | .limitToken => 17
  | .limitDepth => 18
  | .limitEntityExpansion => 19
def report (s : Stream) : Stream :=
  let code :=
    match s.status with
    | .failed e => errorIndex e.code
    | _ => 255
  let offset :=
    match s.status with
    | .failed e => e.offset
    | _ => s.rawConsumed
  let line :=
    match s.status with
    | .failed _ => s.failLine
    | _ => s.line
  let column :=
    match s.status with
    | .failed _ => s.failColumn
    | _ => s.column
  let result := reportStatus (statusCode s) code (UInt64.ofNat offset)
    (UInt64.ofNat line) (UInt64.ofNat column) (UInt64.ofNat s.rawConsumed)
  if result == 0xFFFFFFFFFFFFFFFF then { s with failSet := true } else s
def streamNew (_hint : UInt64) : Stream :=
  Stream.new
def streamFeed (s : Stream) (bytes : ByteArray) : Stream :=
  let base := s.rawConsumed + s.tagCarry.size
  report (Stream.feedSink (emit base) s bytes)
def streamFinish (s : Stream) : Stream :=
  report (Stream.finishSink (fun _ e => emit 0 ByteArray.empty e) s)
end LexPat.CAbi


