-- Prove2me | Definitions.Def_LexPat_Types
-- name    : LexPat_Types
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:33:46.538278+00:00
-- url     : https://prove2.me/theorems/3e23189b-3557-4568-baec-5f66139e23af
-- title:
--   Types
-- statement:
--   Definitions and structural lemmas for Types, from scidonia/lexpat contributors (see pinned LICENSE and source headers)'s pinned UTF-8 decoder properties for LexPat development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scidonia/lexpat/blob/15eee92b433940e5481f09c7f77e6f833e5f684d/LexPat/Types.lean

set_option autoImplicit true
namespace LexPat
structure Scalar where
  n : Nat
  valid : Nat.isValidChar n
namespace Scalar
instance : Inhabited Scalar := ⟨⟨0x41, by decide⟩⟩
instance : Repr Scalar := ⟨fun s _ => repr s.n⟩
instance : BEq Scalar := ⟨fun a b => a.n == b.n⟩
def toChar (s : Scalar) : Char := Char.ofNat s.n
end Scalar
structure DecodedChar where
  value : Scalar
  byteOffset : Nat
deriving Repr
inductive Encoding where
  | utf8
  | utf16le
  | utf16be
  | latin1
  | ascii
deriving DecidableEq, Repr
namespace Encoding
def name : Encoding → String
  | .utf8 => "UTF-8"
  | .utf16le => "UTF-16LE"
  | .utf16be => "UTF-16BE"
  | .latin1 => "ISO-8859-1"
  | .ascii => ("US-ASCII")
end Encoding
inductive ErrorCode where
  | syntaxErr
  | noElements
  | invalidToken
  | unclosedToken
  | partialChar
  | tagMismatch
  | duplicateAttribute
  | junkAfterDocElement
  | undefinedEntity
  | badCharRef
  | misplacedXmlPi
  | unknownEncoding
  | incorrectEncoding
  | unclosedCdataSection
  | xmlDecl
  | unsupportedDtd
  | limitInput
  | limitToken
  | limitDepth
  | limitEntityExpansion
deriving DecidableEq, Repr
namespace ErrorCode
def name : ErrorCode → String
  | .syntaxErr => "SYNTAX"
  | .noElements => "NO_ELEMENTS"
  | .invalidToken => "INVALID_TOKEN"
  | .unclosedToken => "UNCLOSED_TOKEN"
  | .partialChar => "PARTIAL_CHAR"
  | .tagMismatch => "TAG_MISMATCH"
  | .duplicateAttribute => "DUPLICATE_ATTRIBUTE"
  | .junkAfterDocElement => "JUNK_AFTER_DOC_ELEMENT"
  | .undefinedEntity => "UNDEFINED_ENTITY"
  | .badCharRef => "BAD_CHAR_REF"
  | .misplacedXmlPi => "MISPLACED_XML_PI"
  | .unknownEncoding => "UNKNOWN_ENCODING"
  | .incorrectEncoding => "INCORRECT_ENCODING"
  | .unclosedCdataSection => "UNCLOSED_CDATA_SECTION"
  | .xmlDecl => "XML_DECL"
  | .unsupportedDtd => "UNSUPPORTED_DTD"
  | .limitInput => "LIMIT_INPUT"
  | .limitToken => "LIMIT_TOKEN"
  | .limitDepth => "LIMIT_DEPTH"
  | .limitEntityExpansion => ("LIMIT_ENTITY_EXPANSION")
end ErrorCode
inductive DecodeReason where
  | invalidLead
  | invalidContinuation
  | overlong
  | surrogate
  | outOfRange
  | truncated
  | oddUtf16Length
  | unpairedSurrogate
  | invalidAscii
  | unknownEncoding
  | encodingMismatch
deriving DecidableEq, Repr
namespace DecodeReason
def name : DecodeReason → String
  | .invalidLead => "invalidLead"
  | .invalidContinuation => "invalidContinuation"
  | .overlong => "overlong"
  | .surrogate => "surrogate"
  | .outOfRange => "outOfRange"
  | .truncated => "truncated"
  | .oddUtf16Length => "oddUtf16Length"
  | .unpairedSurrogate => "unpairedSurrogate"
  | .invalidAscii => "invalidAscii"
  | .unknownEncoding => "unknownEncoding"
  | .encodingMismatch => ("encodingMismatch")
def code : DecodeReason → ErrorCode
  | .invalidLead => .invalidToken
  | .invalidContinuation => .invalidToken
  | .overlong => .invalidToken
  | .surrogate => .invalidToken
  | .outOfRange => .invalidToken
  | .truncated => .partialChar
  | .oddUtf16Length => .partialChar
  | .unpairedSurrogate => .invalidToken
  | .invalidAscii => .invalidToken
  | .unknownEncoding => .unknownEncoding
  | .encodingMismatch => .incorrectEncoding
end DecodeReason
structure DecodeError where
  reason : DecodeReason
  offset : Nat
deriving DecidableEq, Repr
structure ParseError where
  code : ErrorCode
  reason : String
  offset : Nat
deriving Repr
structure Limits where
  maxInputBytes : Nat := 8 * 1024 * 1024
  maxTokenChars : Nat := 1024 * 1024
  maxDepth : Nat := 256
  maxEntityExpansion : Nat := 1024 * 1024
deriving Repr, DecidableEq, Inhabited
inductive Event where
  | xmlDecl (version : String) (encoding : Option String) (standalone : Option Bool)
  | start (name : String) (attributes : Array (String × String))
  | end (name : String)
  | text (data : String)
  | cdataStart
  | cdataEnd
  | comment (data : String)
  | pi (target : String) (data : String)
deriving Repr, DecidableEq, BEq
structure Span where
  start : Nat
  stop : Nat
deriving Repr, DecidableEq
structure LocatedEvent where
  event : Event
  byteOffset : Nat
  tokenBytes : Option Nat
  line : Nat
  column : Nat
  specifiedAttrs : Nat
  textSpan : Option Span := none
  /-- The token's own UTF-8 bytes when no chunk span can name them. It is read
  with an explicit length, so it needs no NUL terminator, and it stays owned by
  the event until the event is released. -/
  textBytes : Option ByteArray := none
  /-- For a start event whose element name and ordered attribute pairs are still
  spans of the buffer that was scanned: the name's byte range and, for each
  attribute pair, four numbers (name start, name stop, value start, value stop),
  all relative to that buffer. A consumer that needs owned text uses the `Event`
  payload the emitter already built; a consumer that copies into its own arena
  can read these ranges and copy once. -/
  nameSpan : Option Span := none
  attrRanges : Option (Array UInt64) := none
  /-- The absolute offset of the first byte of the buffer `nameSpan` and
  `attrRanges` are relative to. It differs from the feeding chunk's base when a
  start tag was committed from bytes held over a feed boundary. Text spans always
  refer to the chunk being fed. -/
  sliceBase : Nat := 0
def reprTextBytes : Option ByteArray → String
  | none => "none"
  | some bytes => ("some (" ++ toString bytes.size ++ " bytes)")
instance : Repr LocatedEvent where
  reprPrec e prec :=
    reprPrec (e.event, e.byteOffset, e.tokenBytes, e.line, e.column,
              e.specifiedAttrs, e.textSpan, reprTextBytes e.textBytes, e.nameSpan,
              e.attrRanges, e.sliceBase) prec
end LexPat


