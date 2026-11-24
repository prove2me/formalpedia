-- Prove2me | Definitions.Def_LexPat_Stream
-- name    : LexPat_Stream
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:16:22.787516+00:00
-- url     : https://prove2.me/theorems/143f9477-0581-48f6-9ce0-05f77105d33c
-- title:
--   Stream
-- statement:
--   Definitions and structural lemmas for Stream, from scidonia/lexpat contributors (see pinned LICENSE and source headers)'s pinned UTF-8 decoder properties for LexPat development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scidonia/lexpat/blob/15eee92b433940e5481f09c7f77e6f833e5f684d/LexPat/Stream.lean

import Definitions.Def_LexPat_Types
import Definitions.Def_LexPat_Lexer
import Definitions.Def_LexPat_Encoding
import Definitions.Def_LexPat_Grammar
set_option autoImplicit true
namespace LexPat
inductive StreamStatus where
  /-- More bytes may still change or complete the document. -/
  | active
  /-- A permanent error: `feed` and `finish` are inert. -/
  | failed (error : ParseError)
  /-- A complete document: `feed` and `finish` are inert. -/
  | done
deriving Repr
inductive EncPhase where
  | probing (bytes : ByteArray)
  | declaration (bytes : ByteArray)
  | decided (encoding : Encoding)
inductive RefCtx where
  | text
  | attribute (quote : Char)
deriving Repr
inductive DeclMode where
  | needWs1
  | versionNameSkipWs
  | versionName
  | versionAfterName
  | versionAfterEq
  | versionValue (quote : Char)
  | versionDone (sawSep : Bool)
  | versionQ (sawSep : Bool)
  | secondName
  | secondAfterName
  | secondAfterEq
  | secondValue (quote : Char)
  | standaloneDone (which : Nat)
  | standaloneQ (which : Nat)
  | encodingDone (sawSep : Bool)
  | encodingQ (sawSep : Bool)
  | thirdName
  | thirdAfterName
  | thirdAfterEq
  | thirdValue (quote : Char)
  | thirdDone
  | thirdQ
deriving Repr
inductive DeclNameStage where
  | version
  | second
  | third
deriving Repr
inductive Mode where
  | prologStart
  | epilogStart
  | contentStart
  | text
  | textBracket1
  | textBracket2
  | markup
  | bang
  | bangDash
  | bangCdata (matched : Nat)
  | bangDoctype (matched : Nat)
  | endName
  | endNameRest
  | endClose (name : String)
  | piTarget
  | piTargetRest
  | piAfterTarget (target : String)
  | piSkipWs (target : String)
  | piQInit (target : String)
  | piData (target : String)
  | piQ (target : String)
  | comment
  | commentDash1
  | commentDash2
  | cdata
  | cdataBracket1
  | cdataBracket2
  | startNameRest
  | startAfterName
  | startSlash
  | attrNameRest
  | attrAfterName
  | attrAfterEq
  | attrValue (quote : Char)
  | refAfterAmp
  | refNameRest
  | refNumOptX
  | refNumDigits (hex : Bool) (value : Nat) (digits : Nat) (overflow : Bool)
  | decl (stage : DeclMode)
deriving Repr
structure Stream where
  /-- Per-document budgets, fixed at construction. -/
  limits : Limits
  status : StreamStatus := .active
  phase : Phase := .prolog
  mode : Mode := .prologStart
  enc : EncPhase := .probing ByteArray.empty
  /-- While a recognized declaration prefix is buffered, `mode`, `buf` and the
  `decl*` fields hold that prefix's declaration grammar state, so a completed
  token the grammar already rejects is reported before the raw-input budget can
  stop the scan. Replaying the prefix through the chosen decoder resets them.
  A non-ASCII byte outside the ASCII-constrained pseudo-attribute names and
  values clears the flag, because the buffered bytes no longer determine the
  declaration; inside such a field it is a certain fault instead. The flag is
  also `false` once a completed declaration makes the shadow unnecessary,
  because all supported encodings agree on ASCII bytes. -/
  declShadow : Bool := true
  /-- Unconsumed bytes of the next decoded scalar (at most three UTF-8 bytes or
  an odd UTF-16 byte or high-surrogate unit). -/
  pending : ByteArray := ByteArray.empty
  pendingOffset : Nat := 0
  /-- The unfinished lexical value: name, attribute value, comment, CDATA, PI
  data or declaration value. Character text has its own byte accumulator, so a
  plain text run never pays one `Array Char` push per scalar. -/
  buf : Array Char := #[]
  /-- UTF-8 pieces of the unfinished text token, in order: one validated span per
  chunk-local literal run, one expansion per reference and one encoding per
  normalized line ending. Appending a piece copies that piece alone, so a token
  that grows over many feeds costs linear copying instead of re-copying the whole
  prefix; the pieces are joined once when the token is flushed. -/
  textPieces : Array ByteArray := #[]
  /-- Decoded characters in the unfinished text token, charged against
  `maxTokenChars`. Byte length and character count differ for non-ASCII. -/
  textChars : Nat := 0
  /-- Span of the text token inside the chunk currently being fed, while the
  token is still one contiguous literal run. Cleared (and its bytes taken as a
  piece) by any append, any conversion, and at the end of the feed, so no state
  ever holds a reference to a consumed chunk. A span exists only while the token
  has no earlier piece. -/
  textSpan : Option Span := none
  /-- The open elements, innermost first. A name is owned because it must
  outlive the chunk it was read from. The stack is pushed and popped at the
  head, so nesting costs one cell per element instead of copying the whole
  stack. -/
  stack : List String := []
  /-- The number of open elements, so the depth budget is checked without
  walking `stack`. -/
  depth : Nat := 0
  entityUsed : Nat := 0
  elemName : String := ""
  attrs : Array (String × String) := #[]
  attrName : String := ""
  markupOffset : Nat := 0
  markupIndex : Nat := 0
  /-- The bytes of an unfinished start tag whose first byte is determined and
  whose remainder has not arrived. They are held **unconsumed**: no budget is
  charged and no position advances until the tag is committed, so its anchors
  and limits are those of its first byte. Bounded by `tagCarryLimit`, never a
  reference to a consumed chunk. -/
  tagCarry : ByteArray := ByteArray.empty
  /-- Bytes this carry has copied so far. A carried start tag appends the new
  bytes and is rescanned, which keeps a tag that arrives in small chunks on the
  scanner instead of the per-byte machine; this budget bounds the total copying
  per tag, so a very long tag cannot make the append quadratic. -/
  tagCarryCopied : Nat := 0
  /-- Set once the start-tag scanner refused the current tag in the current
  feed. Every condition that makes it refuse is still ahead in the remaining
  bytes, so a retry from a later byte of the same feed would scan the same
  remaining bytes and refuse again: at most one attempt is made per feed. -/
  bulkTagTried : Bool := false
  spaced : Bool := false
  /-- A literal CR whose normalized character waits for an optional LF. -/
  pendingCR : Bool := false
  refCtx : RefCtx := .text
  refStartOffset : Nat := 0
  refBuf : Array Char := #[]
  declEncoding : Option String := none
  declStandalone : Option Bool := none
  /-- `some true` for `encoding`, `some false` for `standalone`. -/
  declSecond : Option Bool := none
  /-- Decoded characters consumed so far; used for the declaration-position
  check, not as a byte offset. -/
  charIndex : Nat := 0
  /-- Raw bytes charged against the input budget, including signature bytes
  and an undecided prefix. -/
  rawConsumed : Nat := 0
  /-- The 1-based line and 0-based scalar column of the next decoded scalar. -/
  line : Nat := 1
  column : Nat := 0
  /-- Line and column of the scalar currently being processed, used to anchor
  a markup token at its opening `<`. -/
  charLine : Nat := 1
  charColumn : Nat := 0
  /-- Whether the previous decoded scalar was a raw CR; a following LF then
  completes the same line ending. -/
  prevRawCR : Bool := false
  /-- Location of the `<` that opened the current markup token. -/
  markupLine : Nat := 1
  markupColumn : Nat := 0
  /-- Start of the text token being accumulated; a reference marker counts as
  its first byte when the text begins with one. -/
  textOffset : Nat := 0
  textLine : Nat := 1
  textColumn : Nat := 0
  textStarted : Bool := false
  /-- Candidate `]]>` closing-marker start in a CDATA section, and the last
  `]` consumed in bracket state so the candidate can advance. -/
  cdataCloseOffset : Nat := 0
  cdataCloseLine : Nat := 1
  cdataCloseColumn : Nat := 0
  lastBracketOffset : Nat := 0
  lastBracketLine : Nat := 1
  lastBracketColumn : Nat := 0
  /-- The first failure's source location, once one has been recorded. -/
  failLine : Nat := 1
  failColumn : Nat := 0
  failSet : Bool := false
namespace Stream
def new (limits : Limits := {}) : Stream :=
  { limits := limits }
def result (s : Stream) : Option (Except ParseError Unit) :=
  match s.status with
  | .active => none
  | .failed e => some (.error e)
  | .done => some (.ok ())
def isActive (s : Stream) : Bool :=
  match s.status with
  | .active => true
  | _ => false
def failedWith (s : Stream) (e : ParseError) : Stream :=
  { s with status := .failed e }
def failCode (s : Stream) (code : ErrorCode) (reason : String) (offset : Nat) :
    Stream :=
  failedWith s ⟨code, reason, offset⟩
def failHere (s : Stream) (code : ErrorCode) (reason : String)
    (offset : Nat) : Stream :=
  let s1 := failCode s code reason offset
  if s1.failSet then s1
  else { s1 with failLine := s.line, failColumn := s.column, failSet := true }
def failAtMarkup (s : Stream) (code : ErrorCode) (reason : String) : Stream :=
  let s1 := failCode s code reason s.markupOffset
  if s1.failSet then s1
  else { s1 with failLine := s.markupLine, failColumn := s.markupColumn, failSet := true }
def noteFailure (s : Stream) : Stream :=
  match s.status with
  | .failed _ =>
    if s.failSet then s
    else { s with failLine := s.line, failColumn := s.column, failSet := true }
  | _ => s
def noteFailure2 (p : Stream × Array LocatedEvent) :
    Stream × Array LocatedEvent :=
  (noteFailure p.1, p.2)
def atMarkup (s : Stream) (event : Event) (pairs : Nat := 0) : LocatedEvent :=
  { event := event
    byteOffset := s.markupOffset
    tokenBytes := some (s.rawConsumed - s.markupOffset)
    line := s.markupLine
    column := s.markupColumn
    specifiedAttrs := pairs }
def atText (s : Stream) (event : Event) : LocatedEvent :=
  { event := event
    byteOffset := s.textOffset
    tokenBytes := none
    line := s.textLine
    column := s.textColumn
    specifiedAttrs := 0 }
def atTextWithSpan (s : Stream) (sp : Span) : LocatedEvent :=
  { event := .text ""
    byteOffset := s.textOffset
    tokenBytes := none
    line := s.textLine
    column := s.textColumn
    specifiedAttrs := 0
    textSpan := some sp }
def atTextBytes (s : Stream) (bytes : ByteArray) : LocatedEvent :=
  { event := .text ""
    byteOffset := s.textOffset
    tokenBytes := none
    line := s.textLine
    column := s.textColumn
    specifiedAttrs := 0
    textBytes := some bytes }
def atCdataClose (s : Stream) : LocatedEvent :=
  { event := .cdataEnd
    byteOffset := s.cdataCloseOffset
    tokenBytes := some (s.rawConsumed - s.cdataCloseOffset)
    line := s.cdataCloseLine
    column := s.cdataCloseColumn
    specifiedAttrs := 0 }
def noteTextStart (s : Stream) (offset line column : Nat) : Stream :=
  if s.textStarted then s
  else { s with textOffset := offset, textLine := line, textColumn := column,
                textStarted := true }
def pushEvents (acc : Array LocatedEvent) (evs : Array LocatedEvent) : Array LocatedEvent :=
  if evs.isEmpty then acc
  else Id.run do
    let mut out := acc
    for e in evs do
      out := out.push e
    return out
def bufferString (buf : Array Char) : String :=
  String.ofList buf.toList
def scalarUtf8 (n : Nat) : ByteArray :=
  if n < 0x80 then
    ByteArray.mk #[UInt8.ofNat n]
  else if n < 0x800 then
    ByteArray.mk #[UInt8.ofNat (0xC0 + n / 0x40),
                   UInt8.ofNat (0x80 + n % 0x40)]
  else if n < 0x10000 then
    ByteArray.mk #[UInt8.ofNat (0xE0 + n / 0x1000),
                   UInt8.ofNat (0x80 + (n / 0x40) % 0x40),
                   UInt8.ofNat (0x80 + n % 0x40)]
  else
    ByteArray.mk #[UInt8.ofNat (0xF0 + n / 0x40000),
                   UInt8.ofNat (0x80 + (n / 0x1000) % 0x40),
                   UInt8.ofNat (0x80 + (n / 0x40) % 0x40),
                   UInt8.ofNat (0x80 + n % 0x40)]
def appendTextScalar (s : Stream) (n : Nat) (offset : Nat) :
    Stream × Option ParseError :=
  if s.textChars >= s.limits.maxTokenChars then
    (s, some ⟨.limitToken, "limitToken", offset⟩)
  else
    ({ s with textPieces := s.textPieces.push (scalarUtf8 n),
              textChars := s.textChars + 1 }, none)
def joinTextPieces (pieces : Array ByteArray) : ByteArray :=
  if pieces.size == 1 then pieces[0]!
  else pieces.foldl (fun acc piece => acc ++ piece) ByteArray.empty
def stringOfUtf8Validated (bytes : ByteArray) : String :=
  String.fromUTF8! bytes
opaque stringOfUtf8 (bytes : ByteArray) : String := stringOfUtf8Validated bytes
def materializeTextSpan (s : Stream) (owner : ByteArray) : Stream :=
  match s.textSpan with
  | none => s
  | some sp =>
    if sp.start <= sp.stop && sp.stop <= owner.size then
      { s with textPieces := s.textPieces.push (owner.extract sp.start sp.stop),
               textSpan := none }
    else { s with textSpan := none }
def materializeAttrs (chunk : ByteArray) (ranges : Array UInt64) :
    Array (String × String) :=
  Id.run do
    let mut out : Array (String × String) := #[]
    let mut k := 0
    while k + 3 < ranges.size do
      let anStart := (ranges[k]!).toNat
      let anStop := (ranges[k + 1]!).toNat
      let vStart := (ranges[k + 2]!).toNat
      let vStop := (ranges[k + 3]!).toNat
      out := out.push
        (stringOfUtf8 (chunk.extract anStart anStop),
         stringOfUtf8 (chunk.extract vStart vStop))
      k := k + 4
    return out
def materializeEvent (owner : ByteArray) (e : LocatedEvent) : LocatedEvent :=
  match e.textBytes with
  | some bytes =>
    { e with event := .text (stringOfUtf8 bytes), textBytes := none }
  | none =>
    match e.textSpan with
    | some sp =>
      if sp.start <= sp.stop && sp.stop <= owner.size then
        { e with event := .text (stringOfUtf8 (owner.extract sp.start sp.stop)),
                 textSpan := none }
      else { e with event := .text "", textSpan := none }
    | none =>
      -- A bulk start event keeps its attribute table as ranges; the public
      -- `Event` array needs the pairs themselves.
      match e.event, e.attrRanges with
      | .start name #[], some ranges => { e with event := .start name (materializeAttrs owner ranges) }
      | _, _ => e
@[inline] def asciiNameChar (b : UInt8) : Bool :=
  (b ≥ 0x61 && b ≤ 0x7A) || (b ≥ 0x41 && b ≤ 0x5A) || (b ≥ 0x30 && b ≤ 0x39) ||
    b == 0x3A || b == 0x5F || b == 0x2D || b == 0x2E
@[inline] def asciiNameStart (b : UInt8) : Bool :=
  (b ≥ 0x61 && b ≤ 0x7A) || (b ≥ 0x41 && b ≤ 0x5A) || b == 0x3A || b == 0x5F
def isPlainTextByte (b : UInt8) : Bool :=
  b.toNat >= 0x20 && b.toNat < 0x80 && b != 0x3C && b != 0x26 && b != 0x5D &&
    b != 0x0D && b != 0x0A
@[inline] def byteAt (chunk : ByteArray) (k : Nat) : UInt8 :=
  if h : k < chunk.size then chunk[k]'h else 0
def nameEnd (chunk : ByteArray) (limit : Nat) (k : Nat) : Nat :=
  if h : k < chunk.size then
    if k < limit && asciiNameChar (chunk[k]'h) then nameEnd chunk limit (k + 1) else k
  else k
termination_by chunk.size - k
def rangeEqFrom (chunk : ByteArray) (a0 b0 n k : Nat) : Bool :=
  if k < n then
    if byteAt chunk (a0 + k) == byteAt chunk (b0 + k) then rangeEqFrom chunk a0 b0 n (k + 1)
    else false
  else true
termination_by n - k
def rangeEq (chunk : ByteArray) (a0 a1 b0 b1 : Nat) : Bool :=
  if a1 - a0 != b1 - b0 then false
  else rangeEqFrom chunk a0 b0 (a1 - a0) 0
def rangeCompareFrom (chunk : ByteArray) (a b : Span) (k : Nat) : Ordering :=
  if h : k < a.stop - a.start then
    if k < b.stop - b.start then
      let x := byteAt chunk (a.start + k)
      let y := byteAt chunk (b.start + k)
      if x < y then .lt else if x > y then .gt else rangeCompareFrom chunk a b (k + 1)
    else .gt
  else if k < b.stop - b.start then .lt
  else .eq
termination_by (a.stop - a.start) - k
def rangeCompare (chunk : ByteArray) (a b : Span) : Ordering :=
  rangeCompareFrom chunk a b 0
def hasDuplicateNames (chunk : ByteArray) (names : Array Span) : Bool :=
  if names.size < 2 then false
  else
    let ordered := names.qsort (fun a b => rangeCompare chunk a b == .lt)
    Id.run do
      let mut found := false
      let mut k := 1
      while k < ordered.size && !found do
        match ordered[k - 1]?, ordered[k]? with
        | some a, some b =>
          if rangeEq chunk a.start a.stop b.start b.stop then found := true
        | _, _ => pure ()
        k := k + 1
      return found
def findByte (chunk : ByteArray) (b : UInt8) (k : Nat) : Nat :=
  if h : k < chunk.size then
    if (chunk[k]'h) == b then k else findByte chunk b (k + 1)
  else k
termination_by chunk.size - k
def spaceEnd (chunk : ByteArray) (k : Nat) : Nat :=
  if h : k < chunk.size then
    if (chunk[k]'h) == 0x20 then spaceEnd chunk (k + 1) else k
  else k
termination_by chunk.size - k
def attrValueEnd (chunk : ByteArray) (q : UInt8) (k : Nat) : Nat :=
  if h : k < chunk.size then
    let d := chunk[k]'h
    if d != q && d != 0x3C && d != 0x26 && d.toNat >= 0x20 && d.toNat < 0x80 then
      attrValueEnd chunk q (k + 1)
    else k
  else k
termination_by chunk.size - k
def plainTextEnd (chunk : ByteArray) (limit : Nat) (k : Nat) : Nat :=
  if h : k < chunk.size then
    if k < limit && isPlainTextByte (chunk[k]'h) then plainTextEnd chunk limit (k + 1)
    else k
  else k
termination_by chunk.size - k
inductive TermEnd where
  /-- The terminator begins here. -/
  | at (k : Nat)
  /-- A byte the construct may not contain, which the per-byte machine reports
  with its own reason and offset. -/
  | illegal
  /-- The terminator is not in these bytes. -/
  | missing
def commentEnd (chunk : ByteArray) (k : Nat) : TermEnd :=
  if k + 2 < chunk.size then
    if byteAt chunk k == 0x2D && byteAt chunk (k + 1) == 0x2D &&
        byteAt chunk (k + 2) == 0x3E then
      .at k
    else
      let d := byteAt chunk k
      if d == 0x2D || d.toNat < 0x20 || d.toNat >= 0x80 then .illegal
      else commentEnd chunk (k + 1)
  else .missing
termination_by chunk.size - k
def cdataEnd (chunk : ByteArray) (k : Nat) : TermEnd :=
  if k + 2 < chunk.size then
    if byteAt chunk k == 0x5D && byteAt chunk (k + 1) == 0x5D &&
        byteAt chunk (k + 2) == 0x3E then
      .at k
    else
      let d := byteAt chunk k
      if d == 0x5D || d.toNat < 0x20 || d.toNat >= 0x80 then .illegal
      else cdataEnd chunk (k + 1)
  else .missing
termination_by chunk.size - k
def piDataEnd (chunk : ByteArray) (k : Nat) : TermEnd :=
  if k + 1 < chunk.size then
    if byteAt chunk k == 0x3F && byteAt chunk (k + 1) == 0x3E then
      .at k
    else
      let d := byteAt chunk k
      if d == 0x3F || d.toNat < 0x20 || d.toNat >= 0x80 then .illegal
      else piDataEnd chunk (k + 1)
  else .missing
termination_by chunk.size - k
def leadLt (chunk : ByteArray) (lead i : Nat) : Bool :=
  lead == 0 || byteAt chunk (i - 1) == 0x3C
def tokenOffset (s : Stream) (lead : Nat) : Nat :=
  if lead == 1 then s.rawConsumed else s.markupOffset
def tokenLine (s : Stream) (lead : Nat) : Nat :=
  if lead == 1 then s.line else s.markupLine
def tokenColumn (s : Stream) (lead : Nat) : Nat :=
  if lead == 1 then s.column else s.markupColumn
def tokenIndex (s : Stream) (lead : Nat) : Nat :=
  if lead == 1 then s.charIndex else s.markupIndex
def tokenContinuation (s : Stream) (lead consumed : Nat)
    (phase : Phase) (mode : Mode) (stack : List String) (depth : Nat)
    (elemName : String) (attrs : Array (String × String)) (buf : Array Char)
    (spaced textStarted : Bool) : Stream :=
  { s with
    rawConsumed := s.rawConsumed + consumed + lead,
    column := s.column + consumed + lead,
    charIndex := s.charIndex + consumed + lead,
    prevRawCR := false,
    markupOffset := tokenOffset s lead,
    markupLine := tokenLine s lead,
    markupColumn := tokenColumn s lead,
    markupIndex := tokenIndex s lead,
    charLine := tokenLine s lead,
    charColumn := tokenColumn s lead,
    phase := phase, mode := mode, stack := stack, depth := depth,
    elemName := elemName, attrs := attrs, buf := buf, spaced := spaced,
    textStarted := textStarted }
def atToken (s : Stream) (lead consumed : Nat) (event : Event)
    (pairs : Nat := 0) (base : Nat := 0) : LocatedEvent :=
  { event := event
    byteOffset := tokenOffset s lead
    tokenBytes := some (consumed + 1)
    line := tokenLine s lead
    column := tokenColumn s lead
    specifiedAttrs := pairs
    sliceBase := base }
def fastTextEligible (s : Stream) : Bool :=
  s.pending.isEmpty && !s.pendingCR &&
    (match s.mode with | .text => true | .contentStart => true | _ => false)
structure TextRun where
  len : Nat := 0
  chars : Nat := 0
  converted : Option ByteArray := none
def scanTextRun (s : Stream) (chunk : ByteArray) (i : Nat) : TextRun :=
  if !fastTextEligible s then {}
  else
    let room := s.limits.maxInputBytes - s.rawConsumed
    match s.enc with
    | .decided .utf8 | .decided .ascii =>
      let stop := plainTextEnd chunk (i + room) i
      { len := stop - i, chars := stop - i }
    | .decided .latin1 =>
      Id.run do
        let mut k := i
        let mut out := ByteArray.empty
        while k < chunk.size && k - i < room &&
            (match chunk[k]? with
             | some b => b.toNat >= 0x20 && b != 0x3C && b != 0x26 && b != 0x5D &&
                 b != 0x0D && b != 0x0A
             | none => false) do
          let b := chunk[k]!
          out := if b.toNat < 0x80 then out.push b
                 else
                   out.push (UInt8.ofNat (0xC0 + b.toNat / 0x40))
                     |>.push (UInt8.ofNat (0x80 + b.toNat % 0x40))
          k := k + 1
        return { len := k - i, chars := k - i, converted := some out }
    | .decided .utf16le => scanTextUtf16 chunk i room false
    | .decided .utf16be => scanTextUtf16 chunk i room true
    | _ => {}
where
  scanTextUtf16 (chunk : ByteArray) (i room : Nat) (bigEndian : Bool) : TextRun :=
    Id.run do
      let mut k := i
      let mut out := ByteArray.empty
      let mut stop := false
      while !stop && k < chunk.size && k - i + 2 <= room do
        match chunk[k]?, chunk[k + 1]? with
        | some b0, some b1 =>
          let u := utf16Unit bigEndian b0 b1
          if u < 0x20 || u >= 0x80 || u == 0x3C || u == 0x26 || u == 0x5D then
            stop := true
          else
            out := out.push (UInt8.ofNat u)
            k := k + 2
        | _, _ => stop := true
      return { len := k - i, chars := (k - i) / 2, converted := some out }
def appendChar (s : Stream) (ch : Char) (offset : Nat) :
    Stream × Option ParseError :=
  if s.buf.size ≥ s.limits.maxTokenChars then
    (s, some ⟨.limitToken, "limitToken", offset⟩)
  else
    -- Take the buffer out of the record before appending, so the append reuses
    -- the array in place: a token built one character at a time must stay linear
    -- in its length, or the token budget itself becomes a quadratic work factor.
    let buf := s.buf
    let cleared := { s with buf := #[] }
    ({ cleared with buf := buf.push ch }, none)
def appendRefChar (s : Stream) (ch : Char) (offset : Nat) :
    Stream × Option ParseError :=
  if s.refBuf.size ≥ s.limits.maxTokenChars then
    (s, some ⟨.limitToken, "limitToken", offset⟩)
  else
    let buf := s.refBuf
    let cleared := { s with refBuf := #[] }
    ({ cleared with refBuf := buf.push ch }, none)
def chargeRefDigit (s : Stream) (digits : Nat) (offset : Nat) :
    Option ParseError :=
  if digits ≥ s.limits.maxTokenChars then
    some ⟨.limitToken, "limitToken", offset⟩
  else none
inductive StepEvents where
  | none
  | one (a : LocatedEvent)
  | two (a b : LocatedEvent)
  | three (a b c : LocatedEvent)
  | four (a b c d : LocatedEvent)
def stepEventsOfFlush (evs : Array LocatedEvent) : StepEvents :=
  match evs[0]? with
  | some e => .one e
  | none => .none
def stepThen : StepEvents → StepEvents → StepEvents
  | .none, b => b
  | a, .none => a
  | .one a, .one b => .two a b
  | .one a, .two b c => .three a b c
  | .one a, .three b c d => .four a b c d
  | _, b => b
def flushTextStep (s : Stream) : Stream × StepEvents :=
  if s.textPieces.isEmpty then
    match s.textSpan with
    | none =>
      -- No token to flush. Copying the stream is what a flush costs a caller
      -- that reaches this branch once per markup token, so a stream that never
      -- started a token is returned as it is.
      (if s.textStarted then { s with textStarted := false } else s, .none)
    | some sp =>
      -- The flushed token ends here, so its character count goes with it: the
      -- budget is per token, and the next token starts from zero however its
      -- bytes were held.
      ({ s with textStarted := false, textSpan := none, textChars := 0 },
       .one (atTextWithSpan s sp))
  else
    -- The token's bytes are already a byte array, and every consumer that
    -- cannot borrow a chunk span can read a length-delimited buffer, so the
    -- flush delivers them as they are. Only the public `Event` API, which
    -- returns `String` payloads, builds a `String` from them.
    let bytes := joinTextPieces s.textPieces
    ({ s with
       textPieces := #[], textChars := 0, textStarted := false, textSpan := none },
     .one (atTextBytes s bytes))
def flushText (s : Stream) (evs : Array LocatedEvent) : Stream × Array LocatedEvent :=
  let (s', step) := flushTextStep s
  match step with
  | .none => (s', evs)
  | .one e => (s', evs.push e)
  | _ => (s', evs)
def resumeMode (phase : Phase) : Mode :=
  match phase with
  | .prolog => .prologStart
  | .content => .contentStart
  | .epilog => .epilogStart
def unknownMarkupError (s : Stream) : ParseError :=
  match s.phase with
  | .prolog => ⟨.syntaxErr, "unknownMarkup", s.markupOffset⟩
  | .content => ⟨.invalidToken, "unknownMarkup", s.markupOffset⟩
  | .epilog => ⟨.junkAfterDocElement, "junkAfterRoot", s.markupOffset⟩
def detectedEncoding (s : Stream) : Encoding :=
  match s.enc with
  | .decided enc => enc
  | _ => .utf8
def hasDuplicateAttr (attrs : Array (String × String)) : Bool :=
  if attrs.size < 2 then false
  else
    let ordered := attrs.qsort (fun a b => a.1 < b.1)
    Id.run do
      let mut found := false
      let mut k := 1
      while k < ordered.size do
        match ordered[k]?, ordered[k - 1]? with
        | some a, some b => if a.1 == b.1 then found := true
        | _, _ => pure ()
        k := k + 1
      return found
def completeStartTag (s : Stream) (empty : Bool) : Stream × Array LocatedEvent :=
  if hasDuplicateAttr s.attrs then
    -- A duplicate attribute is a fault of the whole start tag: report the
    -- opening `<` so the byte index and the line and column name one token.
    (failAtMarkup s .duplicateAttribute "duplicateAttribute", #[])
  else if !empty && s.depth ≥ s.limits.maxDepth then
    (failAtMarkup s .limitDepth "limitDepth", #[])
  else
    let name := s.elemName
    let attrs := s.attrs
    let started : Array LocatedEvent := #[atMarkup s (.start name attrs) attrs.size]
    if empty then
      let evs := started.push (atMarkup s (.end name))
      let phase := if s.phase == .prolog then Phase.epilog else s.phase
      ({ s with phase := phase, mode := resumeMode phase,
                elemName := "", attrs := #[], buf := #[], spaced := false }, evs)
    else
      ({ s with phase := .content, mode := .contentStart,
                stack := name :: s.stack, depth := s.depth + 1,
                elemName := "", attrs := #[], buf := #[], spaced := false }, started)
def finishEndTag (s : Stream) (name : String) : Stream × Array LocatedEvent :=
  match s.stack.head? with
  | some top =>
    if top == name then
      let stack := s.stack.tail
      let evs : Array LocatedEvent := #[atMarkup s (.end name)]
      if stack.isEmpty then
        ({ s with
          stack := stack, depth := s.depth - 1,
          phase := .epilog, mode := .epilogStart }, evs)
      else
        ({ s with
          stack := stack, depth := s.depth - 1, mode := .contentStart }, evs)
    else
      (failAtMarkup s .tagMismatch "tagMismatch", #[])
  | none => (failAtMarkup s .invalidToken "strayEndTag", #[])
def startTagFirst (s : Stream) (c : DecodedChar) : Stream × Array LocatedEvent :=
  if isNameStartChar c.value.n then
    let fresh := { s with buf := #[], elemName := "", attrs := #[], spaced := false }
    match appendChar fresh c.value.toChar c.byteOffset with
    | (s1, some e) => (failedWith s1 e, #[])
    | (s1, none) => ({ s1 with mode := .startNameRest }, #[])
  else (failCode s .invalidToken "invalidNameStart" c.byteOffset, #[])
def emitXmlDecl (s : Stream) : Stream × Array LocatedEvent :=
  ({ s with mode := .prologStart },
    #[atMarkup s (.xmlDecl "1.0" s.declEncoding s.declStandalone)])
def startDeclName (s : Stream) (rest : DeclMode) (c : DecodedChar) :
    Stream × Option ParseError :=
  if isAsciiLetter c.value.n then
    match appendChar { s with buf := #[] } c.value.toChar c.byteOffset with
    | (s1, some err) => (s1, some err)
    | (s1, none) => ({ s1 with mode := .decl rest }, none)
  else
    (s, some ⟨.xmlDecl, "xmlDeclName", c.byteOffset⟩)
def declNameDone (s : Stream) (stage : DeclNameStage) (offset : Nat) :
    Stream × Option ParseError :=
  let name := bufferString s.buf
  let s1 := { s with buf := #[] }
  match stage with
  | .version =>
    if name != "version" then
      (s1, some ⟨.xmlDecl, "xmlDeclVersion", offset⟩)
    else
      ({ s1 with mode := .decl .versionAfterName }, none)
  | .second =>
    if name == "standalone" then
      ({ s1 with mode := .decl .secondAfterName, declSecond := some false }, none)
    else if name == "encoding" then
      ({ s1 with mode := .decl .secondAfterName, declSecond := some true }, none)
    else
      (s1, some ⟨.xmlDecl, "xmlDeclAttribute", offset⟩)
  | .third =>
    if name != "standalone" then
      (s1, some ⟨.xmlDecl, "xmlDeclAttribute", offset⟩)
    else
      ({ s1 with mode := .decl .thirdAfterName }, none)
def nonAsciiDeclFault (s : Stream) : Option (ErrorCode × String) :=
  match s.mode with
  | .decl (.versionName) =>
    if bufferString s.buf == "version" then some (.xmlDecl, "xmlDeclEquals")
    else some (.xmlDecl, "xmlDeclVersion")
  | .decl (.secondName) =>
    let name := bufferString s.buf
    if name == "encoding" || name == "standalone" then
      some (.xmlDecl, "xmlDeclEquals")
    else some (.xmlDecl, "xmlDeclAttribute")
  | .decl (.thirdName) =>
    if bufferString s.buf == "standalone" then some (.xmlDecl, "xmlDeclEquals")
    else some (.xmlDecl, "xmlDeclAttribute")
  | .decl (.versionValue _) => some (.xmlDecl, "xmlDeclVersionValue")
  | .decl (.secondValue _) =>
    match s.declSecond with
    | some true => some (.xmlDecl, "xmlDeclEncodingName")
    | some false => some (.xmlDecl, "xmlDeclStandalone")
    | none => some (.xmlDecl, "xmlDeclAttribute")
  | .decl (.thirdValue _) => some (.xmlDecl, "xmlDeclStandalone")
  | _ => none
def cdataPat : Nat → Option Nat
  | 0 => some 0x5B
  | 1 => some 0x43
  | 2 => some 0x44
  | 3 => some 0x41
  | 4 => some 0x54
  | 5 => some 0x41
  | 6 => some 0x5B
  | _ => none
def doctypePat : Nat → Option Nat
  | 0 => some 0x44
  | 1 => some 0x4F
  | 2 => some 0x43
  | 3 => some 0x54
  | 4 => some 0x59
  | 5 => some 0x50
  | 6 => some 0x45
  | _ => none
def finishReference (s : Stream) (sc : Scalar) : Stream × Array LocatedEvent :=
  if s.entityUsed + 1 > s.limits.maxEntityExpansion then
    (failCode s .limitEntityExpansion "limitEntityExpansion" s.refStartOffset, #[])
  else
    let s1 := { s with entityUsed := s.entityUsed + 1 }
    match s.refCtx with
    | .text =>
      match appendTextScalar s1 sc.n s.refStartOffset with
      | (s2, some e) => (failedWith s2 e, #[])
      | (s2, none) => ({ s2 with mode := .text }, #[])
    | .attribute quote =>
      match appendChar s1 sc.toChar s.refStartOffset with
      | (s2, some e) => (failedWith s2 e, #[])
      | (s2, none) => ({ s2 with mode := .attrValue quote }, #[])
def declStep (cont : Stream → Stream × Array LocatedEvent) (s : Stream)
    (c : DecodedChar) (stage : DeclMode) : Stream × Array LocatedEvent :=
  match stage with
  | .needWs1 =>
    if isXmlWhitespace c.value.n then ({ s with mode := .decl .versionNameSkipWs }, #[])
    else (failCode s .xmlDecl "xmlDeclWhitespace" c.byteOffset, #[])
  | .versionNameSkipWs =>
    if isXmlWhitespace c.value.n then (s, #[])
    else
      match startDeclName s .versionName c with
      | (s1, some e) => (failedWith s1 e, #[])
      | (s1, none) => (s1, #[])
  | .versionName =>
    if isAsciiLetter c.value.n then
      match appendChar s c.value.toChar c.byteOffset with
      | (s1, some e) => (failedWith s1 e, #[])
      | (s1, none) => (s1, #[])
    else
      match declNameDone s .version c.byteOffset with
      | (s1, some e) => (failedWith s1 e, #[])
      | (s1, none) => cont s1
  | .versionAfterName =>
    if isXmlWhitespace c.value.n then (s, #[])
    else if c.value.n == 0x3D then ({ s with mode := .decl .versionAfterEq }, #[])
    else (failCode s .xmlDecl "xmlDeclEquals" c.byteOffset, #[])
  | .versionAfterEq =>
    if isXmlWhitespace c.value.n then (s, #[])
    else if c.value.n == 0x22 || c.value.n == 0x27 then
      ({ s with buf := #[], mode := .decl (.versionValue (Char.ofNat c.value.n)) }, #[])
    else (failCode s .xmlDecl "xmlDeclQuote" c.byteOffset, #[])
  | .versionValue quote =>
    if c.value.n == quote.toNat then
      let value := bufferString s.buf
      let s1 := { s with buf := #[] }
      if value != "1.0" then
        (failCode s1 .xmlDecl "xmlDeclVersionValue" c.byteOffset, #[])
      else ({ s1 with mode := .decl (.versionDone false) }, #[])
    else if isXmlChar c.value.n then
      match appendChar s c.value.toChar c.byteOffset with
      | (s1, some e) => (failedWith s1 e, #[])
      | (s1, none) => (s1, #[])
    else (failCode s .xmlDecl "xmlDeclValue" c.byteOffset, #[])
  | .versionDone sawSep =>
    if isXmlWhitespace c.value.n then ({ s with mode := .decl (.versionDone true) }, #[])
    else if c.value.n == 0x3F then ({ s with mode := .decl (.versionQ sawSep) }, #[])
    else if !sawSep then (failCode s .xmlDecl "xmlDeclSeparator" c.byteOffset, #[])
    else
      match startDeclName s .secondName c with
      | (s1, some e) => (failedWith s1 e, #[])
      | (s1, none) => (s1, #[])
  | .versionQ sawSep =>
    if c.value.n == 0x3E then emitXmlDecl s
    else if !sawSep then (failCode s .xmlDecl "xmlDeclSeparator" c.byteOffset, #[])
    else (failCode s .xmlDecl "xmlDeclName" c.byteOffset, #[])
  | .secondName =>
    if isAsciiLetter c.value.n then
      match appendChar s c.value.toChar c.byteOffset with
      | (s1, some e) => (failedWith s1 e, #[])
      | (s1, none) => (s1, #[])
    else
      match declNameDone s .second c.byteOffset with
      | (s1, some e) => (failedWith s1 e, #[])
      | (s1, none) => cont s1
  | .secondAfterName =>
    if isXmlWhitespace c.value.n then (s, #[])
    else if c.value.n == 0x3D then ({ s with mode := .decl .secondAfterEq }, #[])
    else (failCode s .xmlDecl "xmlDeclEquals" c.byteOffset, #[])
  | .secondAfterEq =>
    if isXmlWhitespace c.value.n then (s, #[])
    else if c.value.n == 0x22 || c.value.n == 0x27 then
      ({ s with buf := #[], mode := .decl (.secondValue (Char.ofNat c.value.n)) }, #[])
    else (failCode s .xmlDecl "xmlDeclQuote" c.byteOffset, #[])
  | .secondValue quote =>
    if c.value.n == quote.toNat then
      let value := bufferString s.buf
      let s1 := { s with buf := #[] }
      match s.declSecond with
      | some false =>
        if value == "yes" then
          ({ s1 with declStandalone := some true,
                     mode := .decl (.standaloneDone 2) }, #[])
        else if value == "no" then
          ({ s1 with declStandalone := some false,
                     mode := .decl (.standaloneDone 2) }, #[])
        else (failCode s1 .xmlDecl "xmlDeclStandalone" c.byteOffset, #[])
      | some true =>
        if !validEncName value then
          (failCode s1 .xmlDecl "xmlDeclEncodingName" c.byteOffset, #[])
        else
          match checkEncodingLabel (detectedEncoding s1) value c.byteOffset with
          | .error e => (failedWith s1 e, #[])
          | .ok () =>
            ({ s1 with declEncoding := some value,
                       mode := .decl (.encodingDone false) }, #[])
      | none => (failCode s1 .xmlDecl "xmlDeclAttribute" c.byteOffset, #[])
    else if isXmlChar c.value.n then
      match appendChar s c.value.toChar c.byteOffset with
      | (s1, some e) => (failedWith s1 e, #[])
      | (s1, none) => (s1, #[])
    else (failCode s .xmlDecl "xmlDeclValue" c.byteOffset, #[])
  | .standaloneDone which =>
    if isXmlWhitespace c.value.n then (s, #[])
    else if c.value.n == 0x3F then
      ({ s with mode := .decl (.standaloneQ which) }, #[])
    else (failCode s .xmlDecl "xmlDeclEnd" c.byteOffset, #[])
  | .standaloneQ _ =>
    if c.value.n == 0x3E then emitXmlDecl s
    else (failCode s .xmlDecl "xmlDeclEnd" c.byteOffset, #[])
  | .encodingDone sawSep =>
    if isXmlWhitespace c.value.n then
      ({ s with mode := .decl (.encodingDone true) }, #[])
    else if c.value.n == 0x3F then
      ({ s with mode := .decl (.encodingQ sawSep) }, #[])
    else if !sawSep then
      (failCode s .xmlDecl "xmlDeclSeparator" c.byteOffset, #[])
    else
      match startDeclName s .thirdName c with
      | (s1, some e) => (failedWith s1 e, #[])
      | (s1, none) => (s1, #[])
  | .encodingQ sawSep =>
    if c.value.n == 0x3E then emitXmlDecl s
    else if !sawSep then (failCode s .xmlDecl "xmlDeclSeparator" c.byteOffset, #[])
    else (failCode s .xmlDecl "xmlDeclName" c.byteOffset, #[])
  | .thirdName =>
    if isAsciiLetter c.value.n then
      match appendChar s c.value.toChar c.byteOffset with
      | (s1, some e) => (failedWith s1 e, #[])
      | (s1, none) => (s1, #[])
    else
      match declNameDone s .third c.byteOffset with
      | (s1, some e) => (failedWith s1 e, #[])
      | (s1, none) => cont s1
  | .thirdAfterName =>
    if isXmlWhitespace c.value.n then (s, #[])
    else if c.value.n == 0x3D then ({ s with mode := .decl .thirdAfterEq }, #[])
    else (failCode s .xmlDecl "xmlDeclEquals" c.byteOffset, #[])
  | .thirdAfterEq =>
    if isXmlWhitespace c.value.n then (s, #[])
    else if c.value.n == 0x22 || c.value.n == 0x27 then
      ({ s with buf := #[], mode := .decl (.thirdValue (Char.ofNat c.value.n)) }, #[])
    else (failCode s .xmlDecl "xmlDeclQuote" c.byteOffset, #[])
  | .thirdValue quote =>
    if c.value.n == quote.toNat then
      let value := bufferString s.buf
      let s1 := { s with buf := #[] }
      if value == "yes" then
        ({ s1 with declStandalone := some true, mode := .decl .thirdDone }, #[])
      else if value == "no" then
        ({ s1 with declStandalone := some false, mode := .decl .thirdDone }, #[])
      else (failCode s1 .xmlDecl "xmlDeclStandalone" c.byteOffset, #[])
    else if isXmlChar c.value.n then
      match appendChar s c.value.toChar c.byteOffset with
      | (s1, some e) => (failedWith s1 e, #[])
      | (s1, none) => (s1, #[])
    else (failCode s .xmlDecl "xmlDeclValue" c.byteOffset, #[])
  | .thirdDone =>
    if isXmlWhitespace c.value.n then (s, #[])
    else if c.value.n == 0x3F then ({ s with mode := .decl .thirdQ }, #[])
    else (failCode s .xmlDecl "xmlDeclEnd" c.byteOffset, #[])
  | .thirdQ =>
    if c.value.n == 0x3E then emitXmlDecl s
    else (failCode s .xmlDecl "xmlDeclEnd" c.byteOffset, #[])
def runStep : Nat → Stream → DecodedChar → Stream × Array LocatedEvent
  | 0, s, _ => (s, #[])
  | fuel + 1, s, c =>
    if !isActive s then (s, #[])
    else if s.pendingCR then
      let mapped : Char := match s.mode with
        | .attrValue _ => ' '
        | _ => '\n'
      let appended : Stream × Option ParseError :=
        match s.mode with
        | .text => appendTextScalar s mapped.toNat c.byteOffset
        | _ => appendChar s mapped c.byteOffset
      match appended with
      | (s1, some e) => (failedWith s1 e, #[])
      | (s1, none) =>
        let s2 := { s1 with pendingCR := false }
        if c.value.n == 0x0A then (s2, #[])
        else runStep fuel s2 c
    else
      let reprocess (s1 : Stream) : Stream × Array LocatedEvent := runStep fuel s1 c
      match s.mode with
      | .prologStart =>
        if isXmlWhitespace c.value.n then (s, #[])
        else if c.value.n == 0x3C then
          ({ s with mode := .markup, markupOffset := c.byteOffset,
                    markupLine := s.charLine, markupColumn := s.charColumn,
                    markupIndex := s.charIndex - 1 }, #[])
        else (failCode s .invalidToken "textBeforeRoot" c.byteOffset, #[])
      | .epilogStart =>
        if isXmlWhitespace c.value.n then (s, #[])
        else if c.value.n == 0x3C then
          ({ s with mode := .markup, markupOffset := c.byteOffset,
                    markupLine := s.charLine, markupColumn := s.charColumn,
                    markupIndex := s.charIndex - 1 }, #[])
        else (failCode s .junkAfterDocElement "textAfterRoot" c.byteOffset, #[])
      | .contentStart =>
        if c.value.n == 0x3C then
          ({ s with mode := .markup, markupOffset := c.byteOffset,
                    markupLine := s.charLine, markupColumn := s.charColumn,
                    markupIndex := s.charIndex - 1 }, #[])
        else reprocess ({ s with mode := .text })
      | .text =>
        if c.value.n == 0x3C then
          let (s1, evs) := flushText s #[]
          ({ s1 with mode := .markup, markupOffset := c.byteOffset,
                     markupLine := s.charLine, markupColumn := s.charColumn,
                     markupIndex := s.charIndex - 1 }, evs)
        else if c.value.n == 0x26 then
          ({ noteTextStart s c.byteOffset s.charLine s.charColumn with
                    mode := .refAfterAmp, refCtx := .text,
                    refStartOffset := c.byteOffset, refBuf := #[] }, #[])
        else if c.value.n == 0x5D then
          ({ noteTextStart s c.byteOffset s.charLine s.charColumn with
                    mode := .textBracket1,
                    lastBracketOffset := c.byteOffset,
                    lastBracketLine := s.charLine,
                    lastBracketColumn := s.charColumn }, #[])
        else if c.value.n == 0x0D then
          ({ noteTextStart s c.byteOffset s.charLine s.charColumn with
                    pendingCR := true }, #[])
        else if isXmlChar c.value.n then
          match appendTextScalar (noteTextStart s c.byteOffset s.charLine s.charColumn)
              c.value.n c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => (s1, #[])
        else (failCode s .invalidToken "illegalXmlChar" c.byteOffset, #[])
      | .textBracket1 =>
        if c.value.n == 0x5D then ({ s with mode := .textBracket2 }, #[])
        else
          match appendTextScalar s 0x5D c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => reprocess ({ s1 with mode := .text })
      | .textBracket2 =>
        if c.value.n == 0x3E then
          (failCode s .invalidToken "cdataEndInText" c.byteOffset, #[])
        else if c.value.n == 0x5D then
          match appendTextScalar s 0x5D c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => ({ s1 with mode := .textBracket2 }, #[])
        else
          match appendTextScalar s 0x5D c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) =>
            match appendTextScalar s1 0x5D c.byteOffset with
            | (s2, some e) => (failedWith s2 e, #[])
            | (s2, none) => reprocess ({ s2 with mode := .text })
      | .markup =>
        match s.phase with
        | .prolog =>
          if c.value.n == 0x3F then ({ s with mode := .piTarget }, #[])
          else if c.value.n == 0x21 then ({ s with mode := .bang }, #[])
          else if c.value.n == 0x2F then
            (failAtMarkup s .invalidToken "strayEndTag", #[])
          else startTagFirst s c
        | .content =>
          if c.value.n == 0x3F then ({ s with mode := .piTarget }, #[])
          else if c.value.n == 0x21 then ({ s with mode := .bang }, #[])
          else if c.value.n == 0x2F then ({ s with mode := .endName }, #[])
          else startTagFirst s c
        | .epilog =>
          if c.value.n == 0x3F then ({ s with mode := .piTarget }, #[])
          else if c.value.n == 0x21 then ({ s with mode := .bang }, #[])
          else if c.value.n == 0x2F then
            (failAtMarkup s .invalidToken "strayEndTag", #[])
          else (failAtMarkup s .junkAfterDocElement "junkAfterRoot", #[])
      | .bang =>
        match s.phase with
        | .epilog =>
          if c.value.n == 0x2D then ({ s with mode := .bangDash }, #[])
          else (failCode s .junkAfterDocElement "junkAfterRoot" s.markupOffset, #[])
        | .prolog | .content =>
          if c.value.n == 0x2D then ({ s with mode := .bangDash }, #[])
          else if c.value.n == 0x44 then ({ s with mode := .bangDoctype 1 }, #[])
          else if c.value.n == 0x5B && s.phase == .content then
            ({ s with mode := .bangCdata 1 }, #[])
          else (failedWith s (unknownMarkupError s), #[])
      | .bangDash =>
        if c.value.n == 0x2D then ({ s with mode := .comment }, #[])
        else (failedWith s (unknownMarkupError s), #[])
      | .bangCdata matched =>
        match cdataPat matched with
        | some expected =>
          if c.value.n == expected then
            if matched + 1 == 7 then
              ({ s with
                  mode := .cdata, buf := #[], textPieces := #[],
                  textChars := 0, textStarted := false },
               #[atMarkup s .cdataStart])
            else ({ s with mode := .bangCdata (matched + 1) }, #[])
          else (failedWith s (unknownMarkupError s), #[])
        | none => (failedWith s (unknownMarkupError s), #[])
      | .bangDoctype matched =>
        match doctypePat matched with
        | some expected =>
          if c.value.n == expected then
            if matched + 1 == 7 then
              (failAtMarkup s .unsupportedDtd "unsupportedDtd", #[])
            else ({ s with mode := .bangDoctype (matched + 1) }, #[])
          else (failedWith s (unknownMarkupError s), #[])
        | none => (failedWith s (unknownMarkupError s), #[])
      | .comment =>
        if c.value.n == 0x2D then ({ s with mode := .commentDash1 }, #[])
        else if c.value.n == 0x0D then ({ s with pendingCR := true }, #[])
        else if isXmlChar c.value.n then
          match appendChar s c.value.toChar c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => (s1, #[])
        else (failCode s .invalidToken "illegalXmlChar" c.byteOffset, #[])
      | .commentDash1 =>
        if c.value.n == 0x2D then ({ s with mode := .commentDash2 }, #[])
        else
          match appendChar s '-' c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => reprocess ({ s1 with mode := .comment })
      | .commentDash2 =>
        if c.value.n == 0x3E then
          let data := bufferString s.buf
          ({ s with mode := resumeMode s.phase, buf := #[] },
           #[atMarkup s (.comment data)])
        else (failCode s .invalidToken "doubleHyphenInComment" c.byteOffset, #[])
      | .cdata =>
        if c.value.n == 0x5D then
          ({ s with mode := .cdataBracket1,
                    lastBracketOffset := c.byteOffset,
                    lastBracketLine := s.charLine,
                    lastBracketColumn := s.charColumn }, #[])
        else if c.value.n == 0x0D then
          ({ noteTextStart s c.byteOffset s.charLine s.charColumn with
                    pendingCR := true }, #[])
        else if isXmlChar c.value.n then
          match appendChar (noteTextStart s c.byteOffset s.charLine s.charColumn)
              c.value.toChar c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => (s1, #[])
        else (failCode s .invalidToken "illegalXmlChar" c.byteOffset, #[])
      | .cdataBracket1 =>
        if c.value.n == 0x5D then
          ({ s with mode := .cdataBracket2,
                    cdataCloseOffset := s.lastBracketOffset,
                    cdataCloseLine := s.lastBracketLine,
                    cdataCloseColumn := s.lastBracketColumn,
                    lastBracketOffset := c.byteOffset,
                    lastBracketLine := s.charLine,
                    lastBracketColumn := s.charColumn }, #[])
        else
          let s0 :=
            if s.textStarted then s
            else { s with textOffset := s.lastBracketOffset,
                          textLine := s.lastBracketLine,
                          textColumn := s.lastBracketColumn,
                          textStarted := true }
          match appendChar s0 ']' c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => reprocess ({ s1 with mode := .cdata })
      | .cdataBracket2 =>
        if c.value.n == 0x3E then
          let data := bufferString s.buf
          let textEvs : Array LocatedEvent :=
            if data.isEmpty then #[] else #[atText s (.text data)]
          ({ s with mode := .contentStart, buf := #[], textStarted := false },
           textEvs.push (atCdataClose s))
        else if c.value.n == 0x5D then
          -- The candidate closing pair advances: the older bracket becomes data.
          let s0 :=
            if s.textStarted then s
            else { s with textOffset := s.cdataCloseOffset,
                          textLine := s.cdataCloseLine,
                          textColumn := s.cdataCloseColumn,
                          textStarted := true }
          match appendChar s0 ']' c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) =>
            ({ s1 with mode := .cdataBracket2,
                       cdataCloseOffset := s1.lastBracketOffset,
                       cdataCloseLine := s1.lastBracketLine,
                       cdataCloseColumn := s1.lastBracketColumn,
                       lastBracketOffset := c.byteOffset,
                       lastBracketLine := s.charLine,
                       lastBracketColumn := s.charColumn }, #[])
        else
          let s0 :=
            if s.textStarted then s
            else { s with textOffset := s.cdataCloseOffset,
                          textLine := s.cdataCloseLine,
                          textColumn := s.cdataCloseColumn,
                          textStarted := true }
          match appendChar s0 ']' c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) =>
            match appendChar s1 ']' c.byteOffset with
            | (s2, some e) => (failedWith s2 e, #[])
            | (s2, none) => reprocess ({ s2 with mode := .cdata })
      | .startNameRest =>
        if isNameChar c.value.n then
          match appendChar s c.value.toChar c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => (s1, #[])
        else
          let name := bufferString s.buf
          reprocess ({ s with elemName := name, buf := #[], mode := .startAfterName, spaced := false })
      | .startAfterName =>
        if isXmlWhitespace c.value.n then ({ s with spaced := true }, #[])
        else if c.value.n == 0x3E then completeStartTag s false
        else if c.value.n == 0x2F then ({ s with mode := .startSlash }, #[])
        else if !s.spaced then
          (failCode s .invalidToken "missingAttributeSeparator" c.byteOffset, #[])
        else if isNameStartChar c.value.n then
          match appendChar { s with buf := #[] } c.value.toChar c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => ({ s1 with mode := .attrNameRest }, #[])
        else (failCode s .invalidToken "invalidNameStart" c.byteOffset, #[])
      | .startSlash =>
        if c.value.n == 0x3E then completeStartTag s true
        else (failCode s .invalidToken "badEmptyTag" c.byteOffset, #[])
      | .attrNameRest =>
        if isNameChar c.value.n then
          match appendChar s c.value.toChar c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => (s1, #[])
        else
          let name := bufferString s.buf
          reprocess ({ s with attrName := name, buf := #[], mode := .attrAfterName })
      | .attrAfterName =>
        if isXmlWhitespace c.value.n then (s, #[])
        else if c.value.n == 0x3D then ({ s with mode := .attrAfterEq }, #[])
        else (failCode s .invalidToken "missingEquals" c.byteOffset, #[])
      | .attrAfterEq =>
        if isXmlWhitespace c.value.n then (s, #[])
        else if c.value.n == 0x22 || c.value.n == 0x27 then
          ({ s with buf := #[], mode := .attrValue (Char.ofNat c.value.n) }, #[])
        else (failCode s .invalidToken "unquotedAttribute" c.byteOffset, #[])
      | .attrValue quote =>
        if c.value.n == quote.toNat then
          let value := bufferString s.buf
          -- Take the pair array out of the record before appending, so the append
          -- reuses it in place: a tag whose attributes arrive one at a time must
          -- stay linear in their number instead of copying the array per pair.
          let attrs := s.attrs
          let next := { s with
            attrs := #[], buf := #[], mode := .startAfterName,
            spaced := false, attrName := "" }
          ({ next with attrs := attrs.push (s.attrName, value) }, #[])
        else if c.value.n == 0x26 then
          ({ s with mode := .refAfterAmp, refCtx := RefCtx.attribute quote,
                    refStartOffset := c.byteOffset, refBuf := #[] }, #[])
        else if c.value.n == 0x3C then
          (failCode s .invalidToken "ltInAttribute" c.byteOffset, #[])
        else if c.value.n == 0x0D then
          ({ s with pendingCR := true }, #[])
        else if c.value.n == 0x0A || c.value.n == 0x09 || c.value.n == 0x20 then
          match appendChar s ' ' c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => (s1, #[])
        else if isXmlChar c.value.n then
          match appendChar s c.value.toChar c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => (s1, #[])
        else (failCode s .invalidToken "illegalXmlChar" c.byteOffset, #[])
      | .endName =>
        if isNameStartChar c.value.n then
          match appendChar { s with buf := #[] } c.value.toChar c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => ({ s1 with mode := .endNameRest }, #[])
        else (failCode s .invalidToken "invalidNameStart" c.byteOffset, #[])
      | .endNameRest =>
        if isNameChar c.value.n then
          match appendChar s c.value.toChar c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => (s1, #[])
        else
          let name := bufferString s.buf
          reprocess ({ s with buf := #[], mode := .endClose name })
      | .endClose name =>
        if isXmlWhitespace c.value.n then (s, #[])
        else if c.value.n == 0x3E then finishEndTag s name
        else (failCode s .invalidToken "badEndTag" c.byteOffset, #[])
      | .piTarget =>
        if isNameStartChar c.value.n then
          match appendChar { s with buf := #[] } c.value.toChar c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => ({ s1 with mode := .piTargetRest }, #[])
        else (failCode s .invalidToken "invalidNameStart" c.byteOffset, #[])
      | .piTargetRest =>
        if isNameChar c.value.n then
          match appendChar s c.value.toChar c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => (s1, #[])
        else
          let target := bufferString s.buf
          let s1 := { s with buf := #[] }
          if target == "xml" then
            if s.phase == .prolog && s.markupIndex == 0 then
              reprocess ({ s1 with mode := .decl .needWs1 })
            else (failAtMarkup s1 .misplacedXmlPi "misplacedXmlDecl", #[])
          else if target.toLower == "xml" then
            (failAtMarkup s1 .invalidToken "reservedPiTarget", #[])
          else reprocess ({ s1 with mode := .piAfterTarget target })
      | .piAfterTarget target =>
        if c.value.n == 0x3F then ({ s with mode := .piQInit target }, #[])
        else if isXmlWhitespace c.value.n then ({ s with mode := .piSkipWs target }, #[])
        else (failCode s .invalidToken "piSyntax" c.byteOffset, #[])
      | .piSkipWs target =>
        if isXmlWhitespace c.value.n then (s, #[])
        else reprocess ({ s with mode := .piData target })
      | .piQInit target =>
        if c.value.n == 0x3E then
          ({ s with mode := resumeMode s.phase }, #[atMarkup s (.pi target "")])
        else (failCode s .invalidToken "piSyntax" c.byteOffset, #[])
      | .piData target =>
        if c.value.n == 0x3F then ({ s with mode := .piQ target }, #[])
        else if c.value.n == 0x0D then ({ s with pendingCR := true }, #[])
        else if isXmlChar c.value.n then
          match appendChar s c.value.toChar c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => (s1, #[])
        else (failCode s .invalidToken "illegalXmlChar" c.byteOffset, #[])
      | .piQ target =>
        if c.value.n == 0x3E then
          let data := bufferString s.buf
          ({ s with mode := resumeMode s.phase, buf := #[] },
           #[atMarkup s (.pi target data)])
        else
          match appendChar s '?' c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => reprocess ({ s1 with mode := .piData target })
      | .refAfterAmp =>
        if c.value.n == 0x23 then ({ s with mode := .refNumOptX }, #[])
        else if isNameChar c.value.n then
          match appendRefChar s c.value.toChar c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => ({ s1 with mode := .refNameRest }, #[])
        else (failCode s .invalidToken "malformedReference" c.byteOffset, #[])
      | .refNameRest =>
        if isNameChar c.value.n then
          match appendRefChar s c.value.toChar c.byteOffset with
          | (s1, some e) => (failedWith s1 e, #[])
          | (s1, none) => (s1, #[])
        else if c.value.n == 0x3B then
          let name := bufferString s.refBuf
          let s1 := { s with refBuf := #[] }
          let resolved : Option Scalar :=
            if name == "amp" then some ⟨0x26, by decide⟩
            else if name == "lt" then some ⟨0x3C, by decide⟩
            else if name == "gt" then some ⟨0x3E, by decide⟩
            else if name == "apos" then some ⟨0x27, by decide⟩
            else if name == "quot" then some ⟨0x22, by decide⟩
            else none
          match resolved with
          | some sc => finishReference s1 sc
          | none => (failCode s1 .undefinedEntity "undefinedEntity" s.refStartOffset, #[])
        else (failCode s .invalidToken "unterminatedReference" c.byteOffset, #[])
      | .refNumOptX =>
        if c.value.n == 0x78 then
          ({ s with mode := .refNumDigits true 0 0 false }, #[])
        else
          match decDigitValue c.value.n with
          | some dv =>
            match chargeRefDigit s 0 c.byteOffset with
            | some e => (failedWith s e, #[])
            | none => ({ s with mode := .refNumDigits false dv 1 false }, #[])
          | none => (failCode s .invalidToken "malformedCharRef" c.byteOffset, #[])
      | .refNumDigits hex value digits overflow =>
        let d := if hex then hexDigitValue c.value.n else decDigitValue c.value.n
        match d with
        | some dv =>
          match chargeRefDigit s digits c.byteOffset with
          | some e => (failedWith s e, #[])
          | none =>
            if overflow then
              ({ s with mode := .refNumDigits hex value (digits + 1) true }, #[])
            else
              let nextValue := value * (if hex then 16 else 10) + dv
              let saturated := nextValue > 0x10FFFF
              let nextMode := Mode.refNumDigits hex
                (if saturated then value else nextValue) (digits + 1) saturated
              ({ s with mode := nextMode }, #[])
        | none =>
          if digits == 0 then
            (failCode s .invalidToken "malformedCharRef" c.byteOffset, #[])
          else if c.value.n == 0x3B then
            if overflow then
              (failCode s .badCharRef "badCharRef" c.byteOffset, #[])
            else if isXmlChar value then
              if h : Nat.isValidChar value then
                finishReference { s with refBuf := #[] } ⟨value, h⟩
              else (failCode s .badCharRef "badCharRef" c.byteOffset, #[])
            else (failCode s .badCharRef "badCharRef" c.byteOffset, #[])
          else (failCode s .invalidToken "unterminatedCharRef" c.byteOffset, #[])
      | .decl stage => declStep reprocess s c stage
def stepChar (s : Stream) (c : DecodedChar) : Stream × Array LocatedEvent :=
  let line := s.line
  let column := s.column
  let n := c.value.n
  let isCR := n == 0x0D
  let isLF := n == 0x0A
  let line' := if isCR || (isLF && !s.prevRawCR) then line + 1 else line
  let column' := if isCR || isLF then 0 else column + 1
  let s0 := { s with charIndex := s.charIndex + 1,
                     charLine := line, charColumn := column,
                     line := line', column := column', prevRawCR := isCR }
  let (s1, evs) := runStep 8 s0 c
  let s2 :=
    match s1.status with
    | .active => s1
    | _ =>
      if s1.failSet then s1
      else { s1 with failLine := line, failColumn := column, failSet := true }
  (s2, evs)
def labelEncoding (buf : Array Char) : Option Encoding :=
  match classifyLabel (bufferString buf) with
  | .utf8 => some .utf8
  | .ascii => some .ascii
  | .latin1 => some .latin1
  | _ => none
inductive ByteOutcome where
  | needMore (s : Stream)
  | progressed (s : Stream) (evs : Array LocatedEvent)
  | failed (s : Stream) (evs : Array LocatedEvent)
def charStep (s : Stream) (c : DecodedChar) : ByteOutcome :=
  let (s1, evs) := stepChar s c
  match s1.status with
  | .active => .progressed s1 evs
  | _ => .failed s1 evs
def decodeUtf8Pending (s : Stream) : ByteOutcome :=
  match decodeUtf8One s.pending 0 with
  | .ok (sc, next) =>
    if next == s.pending.size then
      charStep { s with pending := ByteArray.empty } ⟨sc, s.pendingOffset⟩
    else
      .failed (failHere s .invalidToken "invalidLead" s.pendingOffset) #[]
  | .error e =>
    if e.reason == .truncated then
      .needMore s
    else
      .failed
        (failHere s e.reason.code e.reason.name (s.pendingOffset + e.offset)) #[]
def decodeUtf16Pending (s : Stream) (bigEndian : Bool) : ByteOutcome :=
  match s.pending.size with
  | 2 =>
    match s.pending[0]?, s.pending[1]? with
    | some b0, some b1 =>
      let u := utf16Unit bigEndian b0 b1
      if u < 0xD800 then
        match decodeUtf16One s.pending bigEndian 0 with
        | .ok (sc, _) =>
          charStep { s with pending := ByteArray.empty } ⟨sc, s.pendingOffset⟩
        | .error e =>
          .failed
            (failCode s e.reason.code e.reason.name (s.pendingOffset + e.offset)) #[]
      else if u < 0xDC00 then
        .needMore s
      else
        .failed (failHere s .invalidToken "unpairedSurrogate" s.pendingOffset) #[]
    | _, _ => .needMore s
  | 4 =>
    match decodeUtf16One s.pending bigEndian 0 with
    | .ok (sc, _) =>
      charStep { s with pending := ByteArray.empty } ⟨sc, s.pendingOffset⟩
    | .error e =>
      .failed
        (failHere s e.reason.code e.reason.name (s.pendingOffset + e.offset)) #[]
  | _ => .needMore s
def decodeByte (s : Stream) (b : UInt8) (off : Nat) : ByteOutcome :=
  match s.enc with
  | .decided enc =>
    match enc with
    | .utf8 =>
      if s.pending.isEmpty then
        if h : b.toNat < 0x80 then
          charStep s ⟨⟨b.toNat, Or.inl (by omega)⟩, off⟩
        else
          decodeUtf8Pending
            { s with pending := ByteArray.mk #[b], pendingOffset := off }
      else
        decodeUtf8Pending { s with pending := s.pending.push b }
    | .utf16le =>
      let base := if s.pending.isEmpty then off else s.pendingOffset
      decodeUtf16Pending
        { s with pending := s.pending.push b, pendingOffset := base } false
    | .utf16be =>
      let base := if s.pending.isEmpty then off else s.pendingOffset
      decodeUtf16Pending
        { s with pending := s.pending.push b, pendingOffset := base } true
    | .latin1 =>
      charStep s ⟨⟨b.toNat, Or.inl (by
        have hb := UInt8.toNat_lt b
        omega)⟩, off⟩
    | .ascii =>
      if h : b.toNat < 0x80 then
        charStep s ⟨⟨b.toNat, Or.inl (by omega)⟩, off⟩
      else
        .failed (failHere s .invalidToken "invalidAscii" off) #[]
  | _ => .failed (failHere s .syntaxErr "decoderNotReady" off) #[]
def atMarkupConsumed (s : Stream) (event : Event) (pairs consumed base : Nat) :
    LocatedEvent :=
  { event := event
    byteOffset := s.markupOffset
    tokenBytes := some (s.rawConsumed + consumed - s.markupOffset)
    line := s.markupLine
    column := s.markupColumn
    specifiedAttrs := pairs
    sliceBase := base }
abbrev Bulk := Option (Stream × StepEvents × Nat)
inductive TagScan where
  | done (s : Stream) (evs : StepEvents) (next : Nat)
  | fail (s : Stream)
  | more
  | refuse
def tagCarryLimit : Nat := 64 * 1024
def bulkTokenFault (s : Stream) (offset column : Nat) : Stream :=
  { failCode s .limitToken "limitToken" offset with
    failLine := s.line, failColumn := column, failSet := true }
def scanStartTag (s : Stream) (chunk : ByteArray) (i : Nat)
    (namePrefix : String) (havePrefix : Bool) (lead base : Nat) : TagScan :=
  Id.run do
    let n := chunk.size
    if !havePrefix && !asciiNameStart (byteAt chunk i) then return .refuse
    let nameStart := i
    -- Stop as soon as the name cannot fit the token budget: the per-byte
    -- machine then charges and refuses that exact character, so the scan of a
    -- rejected long name is bounded by the budget instead of its length.
    let nameStop :=
      nameEnd chunk (nameStart + (s.limits.maxTokenChars - namePrefix.length) + 1) i
    if nameStop ≥ n then return .more
    if namePrefix.length + (nameStop - nameStart) > s.limits.maxTokenChars then
      -- The name is already longer than any token may be, and every byte before
      -- the budget's edge was a valid name character: the first character past
      -- the budget is the certain fault, exactly as the per-byte machine reports
      -- it, without accumulating or rescanning the rejected name.
      return .fail
        (bulkTokenFault s
          (s.rawConsumed + lead + (s.limits.maxTokenChars - namePrefix.length))
          (s.column + lead + (nameStart - i + (s.limits.maxTokenChars - namePrefix.length))))
    let mut names : Array Span := #[]
    let mut ranges : Array UInt64 := #[]
    let mut k := nameStop
    let mut empty := false
    let mut done := false
    while !done do
      if k ≥ n then return .more
      else
      let b := byteAt chunk k
      if b == 0x3E then
        done := true
        k := k + 1
      else if b == 0x2F then
        if k + 1 ≥ n then return .more
        if byteAt chunk (k + 1) != 0x3E then return .refuse
        empty := true
        done := true
        k := k + 2
      else if b == 0x20 then
        k := spaceEnd chunk k
        if k ≥ n then return .more
        let c := byteAt chunk k
        if c == 0x3E then
          done := true
          k := k + 1
        else if c == 0x2F then
          if k + 1 ≥ n then return .more
          if byteAt chunk (k + 1) != 0x3E then return .refuse
          empty := true
          done := true
          k := k + 2
        else if asciiNameStart c then
          let anStart := k
          let anStop := nameEnd chunk n k
          if anStop ≥ n then return .more
          if anStop - anStart > s.limits.maxTokenChars then
            return .fail
              (bulkTokenFault s
                (s.rawConsumed + lead + (anStart - i + s.limits.maxTokenChars))
                (s.column + lead + (anStart - i + s.limits.maxTokenChars)))
          let eqAt := spaceEnd chunk anStop
          if eqAt ≥ n then return .more
          if byteAt chunk eqAt != 0x3D then return .refuse
          let quoteAt := spaceEnd chunk (eqAt + 1)
          if quoteAt ≥ n then return .more
          let q := byteAt chunk quoteAt
          if q != 0x22 && q != 0x27 then return .refuse
          let vStart := quoteAt + 1
          let vStop := attrValueEnd chunk q vStart
          if vStop ≥ n then return .more
          if byteAt chunk vStop != q then return .refuse
          if vStop - vStart > s.limits.maxTokenChars then
            return .fail
              (bulkTokenFault s
                (s.rawConsumed + lead + (vStart - i + s.limits.maxTokenChars))
                (s.column + lead + (vStart - i + s.limits.maxTokenChars)))
          ranges := ranges.push (UInt64.ofNat anStart) |>.push (UInt64.ofNat anStop)
            |>.push (UInt64.ofNat vStart) |>.push (UInt64.ofNat vStop)
          names := names.push ⟨anStart, anStop⟩
          k := vStop + 1
        else return .refuse
      else return .refuse
    if hasDuplicateNames chunk names then return .refuse
    if !empty && s.depth ≥ s.limits.maxDepth then return .refuse
    let scanned := stringOfUtf8 (chunk.extract nameStart nameStop)
    let name := if havePrefix then namePrefix ++ scanned else scanned
    let consumed := k - i
    if consumed > s.limits.maxInputBytes - (s.rawConsumed + lead) then return .refuse
    let pairs := ranges.size / 4
    let anchored : LocatedEvent :=
      { atToken s lead consumed (.start name #[]) pairs base with
        event := .start name #[] }
    -- The span ranges are buffer-relative and contiguous only when the whole
    -- name was scanned from this buffer. A name whose head came from an earlier
    -- feed or the encoding probe is not contiguous here, so that event keeps its
    -- owned payload and the sink copies from it.
    let started : LocatedEvent :=
      if havePrefix then
        { anchored with event := .start name (materializeAttrs chunk ranges) }
      else
        { anchored with nameSpan := some ⟨nameStart, nameStop⟩, attrRanges := some ranges }
    let closed : LocatedEvent := atToken s lead consumed (.end name) 0 base
    if empty then
      let phase := if s.phase == .prolog then Phase.epilog else s.phase
      let s2 := tokenContinuation s lead consumed phase (resumeMode phase)
        s.stack s.depth "" #[] #[] false s.textStarted
      let close :=
        if havePrefix then closed
        else { closed with nameSpan := some ⟨nameStart, nameStop⟩ }
      return .done s2 (.two started close) k
    else
      let s2 := tokenContinuation s lead consumed .content .contentStart
        (name :: s.stack) (s.depth + 1) "" #[] #[] false s.textStarted
      return .done s2 (.one started) k
inductive TagStep where
  /-- A committed step. `owner` is the buffer the returned events' spans refer
  to: the chunk being fed, or the carried prefix and chunk a tag was committed
  from. Each event already names its buffer's absolute base. -/
  | step (s : Stream) (evs : StepEvents) (next : Nat) (owner : ByteArray)
  | replay
  | refused
  | pass
namespace TagStep
def isRefused : TagStep → Bool
  | .refused => true
  | _ => false
end TagStep
def openMarkup (s : Stream) : Stream :=
  { s with mode := .markup,
           markupOffset := s.rawConsumed,
           markupLine := s.line,
           markupColumn := s.column,
           markupIndex := s.charIndex,
           charLine := s.line,
           charColumn := s.column,
           rawConsumed := s.rawConsumed + 1,
           charIndex := s.charIndex + 1,
           column := s.column + 1,
           prevRawCR := false }
def hasTagEnd (chunk : ByteArray) (first : Nat) : Bool :=
  findByte chunk 0x3E first < chunk.size
def tagCarryCopyLimit : Nat := 256 * 1024
def tagStepHold (s : Stream) (chunk : ByteArray) (i : Nat) : TagStep :=
  let held := chunk.extract i chunk.size
  -- Bytes are held unconsumed, so they are not charged to the raw-input budget
  -- until they are settled. A hold that would carry the parser past that budget
  -- is refused here, which keeps the budget's exact fault and offset unchanged.
  if held.size ≤ tagCarryLimit && s.rawConsumed + held.size ≤ s.limits.maxInputBytes then
    .step { s with tagCarry := held, tagCarryCopied := 0 } .none chunk.size
      ByteArray.empty
  else .pass
def tagStepExtend (s : Stream) (chunk : ByteArray) : TagStep :=
  let combined := s.tagCarry.append chunk
  if combined.size ≤ tagCarryLimit &&
      s.rawConsumed + combined.size ≤ s.limits.maxInputBytes &&
      (chunk.size * 4 ≥ s.tagCarry.size ||
        s.tagCarryCopied + combined.size ≤ tagCarryCopyLimit) then
    .step { s with
      tagCarry := combined, tagCarryCopied := s.tagCarryCopied + combined.size }
      .none chunk.size ByteArray.empty
  else .replay
def tagStep (s : Stream) (chunk : ByteArray) (i : Nat) (nameHead : String)
    (havePrefix : Bool) (lead chunkBase : Nat) : TagStep :=
  if !s.tagCarry.isEmpty then
    let combined := s.tagCarry.append chunk
    match scanStartTag s combined 0 nameHead havePrefix 0 s.rawConsumed with
    | .done st' evs' j =>
      if j < s.tagCarry.size then .replay
      -- The carried bytes are consumed by the commit, so the continuation must
      -- not still reference them. The events' spans name `combined`, whose first
      -- byte sits at the offset the stream still holds for the tag's start.
      else .step { st' with tagCarry := ByteArray.empty, tagCarryCopied := 0 } evs'
        (j - s.tagCarry.size) combined
    | .fail st' => .step { st' with tagCarry := ByteArray.empty, tagCarryCopied := 0 }
        .none chunk.size ByteArray.empty
    | .more => tagStepExtend s chunk
    | .refuse => .replay
  else
    if !havePrefix && !asciiNameStart (byteAt chunk i) then .pass
    else
      match scanStartTag s chunk i nameHead havePrefix lead chunkBase with
      | .done st' evs' j =>
        .step { st' with tagCarry := ByteArray.empty, tagCarryCopied := 0 } evs' j
          chunk
      | .fail st' =>
        .step { st' with tagCarry := ByteArray.empty, tagCarryCopied := 0 } .none
          chunk.size ByteArray.empty
      | .more =>
        -- The tag continues past this chunk. Consuming the `<` first keeps the
        -- held bytes' anchors and budgets those of the tag's first byte, which
        -- is the shape the carry path resumes from.
        if lead == 1 then tagStepHold (openMarkup s) chunk i
        else tagStepHold s chunk i
      | .refuse => if havePrefix then .refused else .pass
def scanEndTag (s : Stream) (chunk : ByteArray) (i : Nat) (lead base : Nat) :
    Bulk :=
  Id.run do
    let n := chunk.size
    if !leadLt chunk lead i then return none
    let nameStart := i + 1
    if !asciiNameStart (byteAt chunk nameStart) then return none
    let nameStop := nameEnd chunk n nameStart
    if nameStop ≥ n then return none
    if nameStop - nameStart > s.limits.maxTokenChars then return none
    let k0 := spaceEnd chunk nameStop
    if k0 ≥ n then return none
    if byteAt chunk k0 != 0x3E then return none
    let k := k0 + 1
    let name := stringOfUtf8 (chunk.extract nameStart nameStop)
    match s.stack.head? with
    | none => return none
    | some top =>
      if top != name then return none
    let consumed := k - i
    if consumed > s.limits.maxInputBytes - (s.rawConsumed + lead) then return none
    let stack := s.stack.tail
    -- The name was scanned from this chunk, so the sink can copy it from the
    -- span instead of the owned string.
    let ended : LocatedEvent :=
      { atToken s lead consumed (.end name) 0 base with
        nameSpan := some ⟨nameStart, nameStop⟩ }
    let phase := if stack.isEmpty then Phase.epilog else s.phase
    let mode := if stack.isEmpty then Mode.epilogStart else Mode.contentStart
    let continued := tokenContinuation s lead consumed phase mode stack (s.depth - 1)
      s.elemName s.attrs s.buf s.spaced s.textStarted
    return some (continued, .one ended, k)
def scanComment (s : Stream) (chunk : ByteArray) (i : Nat) (lead base : Nat) :
    Bulk :=
  Id.run do
    if !leadLt chunk lead i then return none
    if byteAt chunk i != 0x21 || byteAt chunk (i + 1) != 0x2D ||
        byteAt chunk (i + 2) != 0x2D then
      return none
    let dataStart := i + 3
    match commentEnd chunk dataStart with
    | .illegal => return none
    | .missing => return none
    | .at close =>
      if close - dataStart > s.limits.maxTokenChars then return none
      let consumed := close + 3 - i
      if consumed > s.limits.maxInputBytes - (s.rawConsumed + lead) then return none
      let data := stringOfUtf8 (chunk.extract dataStart close)
      let continued := tokenContinuation s lead consumed s.phase (resumeMode s.phase)
        s.stack s.depth s.elemName s.attrs #[] s.spaced s.textStarted
      let ev : LocatedEvent := atToken s lead consumed (.comment data) 0 base
      return some (continued, .one ev, close + 3)
def isXmlPiTarget (chunk : ByteArray) (start stop : Nat) : Bool :=
  stop - start == 3 &&
    (let b0 := byteAt chunk start
     let b1 := byteAt chunk (start + 1)
     let b2 := byteAt chunk (start + 2)
     (b0 == 0x78 || b0 == 0x58) && (b1 == 0x6D || b1 == 0x4D) &&
       (b2 == 0x6C || b2 == 0x4C))
def scanPi (s : Stream) (chunk : ByteArray) (i : Nat) (lead base : Nat) : Bulk :=
  Id.run do
    let n := chunk.size
    if !leadLt chunk lead i then return none
    if byteAt chunk i != 0x3F then return none
    let targetStart := i + 1
    if !asciiNameStart (byteAt chunk targetStart) then return none
    let targetStop := nameEnd chunk n targetStart
    if targetStop ≥ n then return none
    if targetStop - targetStart > s.limits.maxTokenChars then return none
    if isXmlPiTarget chunk targetStart targetStop then return none
    let target := stringOfUtf8 (chunk.extract targetStart targetStop)
    let mut dataStart := targetStop
    let mut dataStop := targetStop
    let mut stopIndex := 0
    if byteAt chunk targetStop == 0x3F then
      if byteAt chunk (targetStop + 1) != 0x3E then return none
      stopIndex := targetStop + 2
    else if byteAt chunk targetStop == 0x20 then
      let afterSpace := spaceEnd chunk targetStop
      if afterSpace ≥ n then return none
      dataStart := afterSpace
      match piDataEnd chunk afterSpace with
      | .illegal => return none
      | .missing => return none
      | .at j =>
        dataStop := j
        stopIndex := j + 2
      if dataStop - dataStart > s.limits.maxTokenChars then return none
    else return none
    let data := stringOfUtf8 (chunk.extract dataStart dataStop)
    let consumed := stopIndex - i
    if consumed > s.limits.maxInputBytes - (s.rawConsumed + lead) then return none
    let continued := tokenContinuation s lead consumed s.phase (resumeMode s.phase)
      s.stack s.depth s.elemName s.attrs #[] s.spaced s.textStarted
    let ev : LocatedEvent := atToken s lead consumed (.pi target data) 0 base
    return some (continued, .one ev, stopIndex)
def scanCdata (s : Stream) (chunk : ByteArray) (i : Nat) (lead base : Nat) : Bulk :=
  Id.run do
    if !leadLt chunk lead i then return none
    if byteAt chunk i != 0x21 || byteAt chunk (i + 1) != 0x5B ||
        byteAt chunk (i + 2) != 0x43 || byteAt chunk (i + 3) != 0x44 ||
        byteAt chunk (i + 4) != 0x41 || byteAt chunk (i + 5) != 0x54 ||
        byteAt chunk (i + 6) != 0x41 || byteAt chunk (i + 7) != 0x5B then
      return none
    let dataStart := i + 8
    match cdataEnd chunk dataStart with
    | .illegal => return none
    | .missing => return none
    | .at close =>
      if close - dataStart > s.limits.maxTokenChars then return none
      let consumed := close + 3 - i
      if consumed > s.limits.maxInputBytes - (s.rawConsumed + lead) then return none
      let continued := tokenContinuation s lead consumed s.phase .contentStart
        s.stack s.depth s.elemName s.attrs #[] s.spaced false
      -- CDATA content is literal: keep it a span of this chunk and let the
      -- consumer materialize it only if it needs an owned string.
      let textEv : Option LocatedEvent :=
        if close == dataStart then none
        else
          some { event := .text ""
                 byteOffset := tokenOffset s lead + 1 + (dataStart - i)
                 tokenBytes := none
                 line := s.line
                 column := tokenColumn s lead + 1 + (dataStart - i)
                 specifiedAttrs := 0
                 textSpan := some ⟨dataStart, close⟩ }
      let closeEv : LocatedEvent :=
        { event := .cdataEnd
          byteOffset := tokenOffset s lead + 1 + (close - i)
          tokenBytes := some 3
          line := s.line
          column := tokenColumn s lead + 1 + (close - i)
          specifiedAttrs := 0 }
      let opener : LocatedEvent :=
        { atToken s lead consumed .cdataStart 0 base with
          tokenBytes := some (dataStart - i + 1) }
      let evs : StepEvents :=
        match textEv with
        | none => .two opener closeEv
        | some content => .three opener content closeEv
      return some (continued, evs, close + 3)
def markupDispatch (s : Stream) (chunk : ByteArray) (i : Nat) (lead base : Nat) :
    TagStep :=
  if !s.tagCarry.isEmpty then
    -- The carried prefix owns the tag, so this chunk continues it whatever its
    -- first byte is.
    tagStep s chunk i "" false 0 base
  else
  let b := byteAt chunk i
  if b == 0x2F then
    if s.phase == .prolog || s.phase == .epilog then .pass
    else
      match scanEndTag s chunk i lead base with
      | some (st', evs', j) => .step st' evs' j chunk
      | none => .pass
  else if b == 0x21 then
    if byteAt chunk (i + 1) == 0x2D then
      match scanComment s chunk i lead base with
      | some (st', evs', j) => .step st' evs' j chunk
      | none => .pass
    else if byteAt chunk (i + 1) == 0x5B then
      if s.phase == .content then
        match scanCdata s chunk i lead base with
        | some (st', evs', j) => .step st' evs' j chunk
        | none => .pass
      else .pass
    else .pass
  else if b == 0x3F then
    match scanPi s chunk i lead base with
    | some (st', evs', j) => .step st' evs' j chunk
    | none => .pass
  else if asciiNameStart b then
    if s.phase == .epilog then .pass else tagStep s chunk i "" false lead base
  else .pass
def withFlush (flush : StepEvents) (chunk : ByteArray) : TagStep → TagStep
  | .step st' evs' j _ => .step st' (stepThen flush evs') j chunk
  | other => other
def foldMarkup (s : Stream) (chunk : ByteArray) (i : Nat) (base : Nat) : TagStep :=
  if !s.pending.isEmpty || s.pendingCR || !s.tagCarry.isEmpty then .pass
  else if byteAt chunk i != 0x3C then .pass
  else
    let (flushed, flush) := flushTextStep s
    match markupDispatch flushed chunk (i + 1) 1 base with
    | .pass => .pass
    | step => withFlush flush chunk step
def scanTagStep (s : Stream) (chunk : ByteArray) (i : Nat)
    (chunkBase : Nat) : TagStep :=
  -- Bulk scanning reads one byte per character, so it is limited to the
  -- byte-oriented encodings; UTF-16 code units are decoded only by the per-byte
  -- machine.
  match s.enc with
  | .decided .utf8 | .decided .ascii | .decided .latin1 =>
    scanTagStepBytes s chunk i chunkBase
  | _ => .pass
where
  scanTagStepBytes (s : Stream) (chunk : ByteArray) (i : Nat) (chunkBase : Nat) :
      TagStep :=
  match s.mode with
  | .markup =>
    markupDispatch s chunk i 0 chunkBase
  | .text | .contentStart | .prologStart | .epilogStart =>
    foldMarkup s chunk i chunkBase
  | .startNameRest =>
    -- The unfinished name is an `Array Char`; turning it into the scanner's
    -- prefix costs one pass over the token, so it happens only when these bytes
    -- can actually complete the tag. Otherwise the bytes are held unconsumed and
    -- the tag is scanned once, when the terminator arrives.
    let ready := hasTagEnd chunk i
    if s.phase == .epilog then .pass
    else if s.bulkTagTried then .pass
    else if !ready then
      if s.tagCarry.isEmpty then tagStepHold s chunk i else tagStepExtend s chunk
    else
      let carried := bufferString s.buf
      if carried.toList.all (fun c => c.toNat < 0x80) then
        -- A carried prefix is scanned from the start of the combined buffer,
        -- whose first byte is the stream's current offset; a tag scanned in the
        -- chunk itself is indexed from the chunk's first byte.
        tagStep s chunk (if s.tagCarry.isEmpty then i else 0) carried true 0
          (if s.tagCarry.isEmpty then chunkBase else s.rawConsumed)
      else if s.tagCarry.isEmpty then .refused
      -- A name that is not ASCII cannot be scanned in bulk, and the carried
      -- bytes precede this chunk: they must be settled before the per-byte
      -- machine may read past them.
      else .replay
  | _ => .pass
def bulkOpenMarkup (s : Stream) (chunk : ByteArray) (i : Nat) :
    Option (Stream × Array LocatedEvent × Nat) :=
  match s.enc with
  | .decided enc =>
    match enc with
    | .utf8 | .ascii | .latin1 =>
      if !s.pending.isEmpty || s.pendingCR then none
      else if chunk[i]? != some 0x3C then none
      else
        let advanced := openMarkup s
        match s.mode with
        | .text =>
          -- The run ends at this byte: the per-byte machine advances the cursor
          -- and then flushes, so the advance happens first here too.
          let (s1, evs) := flushText advanced #[]
          some (s1, evs, i + 1)
        | .contentStart | .prologStart | .epilogStart => some (advanced, #[], i + 1)
        | _ => none
    | _ => none
  | _ => none
def bulkCharRef (s : Stream) (chunk : ByteArray) (i : Nat) :
    Option (Stream × Nat) :=
  match s.enc, s.mode with
  | .decided .utf8, .text | .decided .utf8, .contentStart
  | .decided .ascii, .text | .decided .ascii, .contentStart
  | .decided .latin1, .text | .decided .latin1, .contentStart =>
    if !s.pending.isEmpty || s.pendingCR then none
    else if chunk[i]? != some 0x26 || chunk[i + 1]? != some 0x23 then none
    else Id.run do
      let mut k := i + 2
      let hex := chunk[k]? == some 0x78
      if hex then k := k + 1
      let mut value := 0
      let mut digits := 0
      let mut overflow := false
      let mut stop := false
      while !stop do
        match chunk[k]? with
        | none => return none
        | some b =>
          match (if hex then hexDigitValue b.toNat else decDigitValue b.toNat) with
          | none => stop := true
          | some dv =>
            digits := digits + 1
            if !overflow then
              let nextValue := value * (if hex then 16 else 10) + dv
              if nextValue > 0x10FFFF then overflow := true else value := nextValue
            k := k + 1
            if digits ≥ s.limits.maxTokenChars then return none
      if digits == 0 then return none
      if overflow then return none
      if chunk[k]? != some 0x3B then return none
      -- The budgets and the XML `Char` range decide refusal; the per-byte
      -- machine is where their exact code and offset are reported.
      if s.entityUsed + 1 > s.limits.maxEntityExpansion then return none
      if s.textChars >= s.limits.maxTokenChars then return none
      if !isXmlChar value then return none
      let consumed := k + 1 - i
      if consumed > s.limits.maxInputBytes - s.rawConsumed then return none
      let started :=
        noteTextStart (materializeTextSpan s chunk) s.rawConsumed s.line s.column
      return some ({ started with
        textPieces := started.textPieces.push (scalarUtf8 value),
        textChars := started.textChars + 1,
        entityUsed := started.entityUsed + 1,
        mode := .text,
        rawConsumed := s.rawConsumed + consumed,
        charIndex := s.charIndex + consumed,
        column := s.column + consumed,
        prevRawCR := false,
        refBuf := #[] }, k + 1)
  | _, _ => none
def deliverEvents (collect : Bool) (owner : ByteArray)
    (sink : ByteArray → LocatedEvent → Bool)
    (acc : Array LocatedEvent) (evs : Array LocatedEvent) :
    Bool × Array LocatedEvent :=
  if evs.isEmpty then (true, acc)
  else Id.run do
    let mut acc := acc
    let mut ok := true
    for e in evs do
      if ok then
        let framed := if collect then materializeEvent owner e else e
        ok := sink owner framed
        if collect then acc := acc.push framed
    return (ok, acc)
def deliverOne (collect : Bool) (owner : ByteArray)
    (sink : ByteArray → LocatedEvent → Bool) (acc : Array LocatedEvent)
    (e : LocatedEvent) : Bool × Array LocatedEvent :=
  let framed := if collect then materializeEvent owner e else e
  let ok := sink owner framed
  (ok, if collect then acc.push framed else acc)
def deliverStep (collect : Bool) (owner : ByteArray)
    (sink : ByteArray → LocatedEvent → Bool) (acc : Array LocatedEvent)
    (evs : StepEvents) : Bool × Array LocatedEvent :=
  match evs with
  | .none => (true, acc)
  | .one a => deliverOne collect owner sink acc a
  | .two a b =>
    match deliverOne collect owner sink acc a with
    | (true, acc) => deliverOne collect owner sink acc b
    | (false, acc) => (false, acc)
  | .three a b c =>
    match deliverOne collect owner sink acc a with
    | (true, acc) => match deliverOne collect owner sink acc b with
      | (true, acc) => deliverOne collect owner sink acc c
      | (false, acc) => (false, acc)
    | (false, acc) => (false, acc)
  | .four a b c d =>
    match deliverOne collect owner sink acc a with
    | (true, acc) => match deliverOne collect owner sink acc b with
      | (true, acc) => match deliverOne collect owner sink acc c with
        | (true, acc) => deliverOne collect owner sink acc d
        | (false, acc) => (false, acc)
      | (false, acc) => (false, acc)
    | (false, acc) => (false, acc)
def feedDecoded (collect : Bool) (sink : ByteArray → LocatedEvent → Bool)
    (s : Stream) (evs : Array LocatedEvent) (data : ByteArray) (base : Nat) :
    Stream × Array LocatedEvent × Bool :=
  Id.run do
    let mut st := s
    let mut acc := evs
    let mut j := 0
    let mut stop := false
    let mut ok := true
    while !stop && j < data.size do
      if !isActive st then
        stop := true
      else
        match data[j]? with
        | some b =>
          j := j + 1
          match decodeByte st b (base + (j - 1)) with
          | .needMore st' => st := st'
          | .progressed st' evs' =>
            let (ok', acc') := deliverEvents collect data sink acc evs'
            st := st'; acc := acc'; ok := ok'
            if !ok then stop := true
          | .failed st' evs' =>
            let (ok', acc') := deliverEvents collect data sink acc evs'
            st := st'; acc := acc'; ok := ok'; stop := true
        | none => stop := true
    return (st, acc, ok)
def chooseEncoding (bytes : ByteArray) (limit : Nat) :
    Except ParseError (Encoding × Nat) :=
  match detectSignature bytes with
  | some (enc, off) => .ok (enc, off)
  | none =>
    match scanDeclLabel bytes limit with
    | none => .ok (.utf8, 0)
    | some label =>
      match classifyLabel label with
      | .utf8 => .ok (.utf8, 0)
      | .ascii => .ok (.ascii, 0)
      | .latin1 => .ok (.latin1, 0)
      | .utf16 => .error ⟨.incorrectEncoding, "encodingMismatch", 0⟩
      | .utf16le => .error ⟨.incorrectEncoding, "encodingMismatch", 0⟩
      | .utf16be => .error ⟨.incorrectEncoding, "encodingMismatch", 0⟩
      | .unknown => .error ⟨.unknownEncoding, "unknownEncoding", 0⟩
inductive ProbeAction where
  | wait
  | decide
  | declaration
  | signature (enc : Encoding) (skip : Nat)
def probeAction (buf : ByteArray) : ProbeAction :=
  if buf[0]? == some 0xEF then
    if buf[1]? == some 0xBB then
      if buf[2]? == some 0xBF then .signature .utf8 3
      else if buf.size ≥ 3 then .decide else .wait
    else if buf.size ≥ 2 then .decide else .wait
  else if buf[0]? == some 0xFF then
    if buf[1]? == some 0xFE then .signature .utf16le 2
    else if buf.size ≥ 2 then .decide else .wait
  else if buf[0]? == some 0xFE then
    if buf[1]? == some 0xFF then .signature .utf16be 2
    else if buf.size ≥ 2 then .decide else .wait
  else if buf[0]? == some 0x00 then
    if buf[1]? == some 0x3C then .signature .utf16be 0
    else if buf.size ≥ 2 then .decide else .wait
  else if buf[0]? == some 0x3C then
    if buf[1]? == some 0x00 then .signature .utf16le 0
    else if buf.size < 2 then .wait
    else if buf[1]? != some 0x3F then .decide
    else if buf.size < 3 then .wait
    else if buf[2]? != some 0x78 then .decide
    else if buf.size < 4 then .wait
    else if buf[3]? != some 0x6D then .decide
    else if buf.size < 5 then .wait
    else if buf[4]? != some 0x6C then .decide
    else if buf.size < 6 then .wait
    else
      match buf[5]? with
      | some w => if isXmlWhitespace w.toNat then .declaration else .decide
      | none => .wait
  else .decide
def replayProbe (collect : Bool) (sink : ByteArray → LocatedEvent → Bool)
    (s : Stream) (enc : Encoding) (skip : Nat) (buf : ByteArray) :
    Stream × Array LocatedEvent × Bool :=
  let fresh : Stream :=
    { s with enc := .decided enc, mode := .prologStart, buf := #[],
             declShadow := true, declEncoding := none, declStandalone := none,
             declSecond := none, spaced := false,
             line := 1, column := 0, prevRawCR := false,
             textStarted := false, failSet := false }
  feedDecoded collect sink fresh #[] (buf.extract skip buf.size) skip
def decideFromProbe (collect : Bool) (sink : ByteArray → LocatedEvent → Bool)
    (s : Stream) (buf : ByteArray) : Stream × Array LocatedEvent × Bool :=
  match chooseEncoding buf s.limits.maxTokenChars with
  | .error e => (noteFailure (failedWith s e), #[], true)
  | .ok (enc, skip) => replayProbe collect sink s enc skip buf
def feedCore (collect : Bool) (sink : ByteArray → LocatedEvent → Bool)
    (s : Stream) (chunk : ByteArray) : Stream × Array LocatedEvent :=
  match s.status with
  | .active =>
    if chunk.size == 0 then (s, #[])
    else
      Id.run do
        -- The absolute offset of this chunk's first byte. A start tag held over
        -- from an earlier feed sits between the consumed prefix and these bytes,
        -- so it is counted here; spans this feed commits name this chunk.
        let feedBase := s.rawConsumed + s.tagCarry.size
        let mut st := { s with bulkTagTried := false }
        let mut acc : Array LocatedEvent := #[]
        let mut i := 0
        let mut stop := false
        while !stop && i < chunk.size do
          if !isActive st then
            stop := true
          else if st.rawConsumed ≥ st.limits.maxInputBytes then
            st := failHere st .limitInput "limitInput" st.rawConsumed
            stop := true
          else
            -- The scanners first try to commit the whole construct that
            -- begins here -- with the `<` that opens it, or a start tag that
            -- may continue past this chunk. What they do not fully understand
            -- falls back to the steps below, and finally to the per-byte
            -- machine, from the unchanged state.
            let step := scanTagStep st chunk i feedBase
            if step.isRefused then st := { st with bulkTagTried := true }
            match step with
            | .step st' evs' j owner =>
              let (ok', acc') := deliverStep collect owner sink acc evs'
              st := st'
              acc := acc'
              i := j
              if !ok' || !isActive st' then stop := true
            | .replay =>
              -- The carried prefix is a tag this scanner cannot commit: charge
              -- its bytes and settle it through the per-byte machine, which is
              -- where those bytes would have gone without the carry.
              let base := st.rawConsumed
              let carried := st.tagCarry
              let settled := { st with
                tagCarry := ByteArray.empty, tagCarryCopied := 0,
                rawConsumed := st.rawConsumed + carried.size }
              let (st1, evs1, ok1) := feedDecoded collect sink settled acc carried base
              st := st1
              acc := evs1
              if !ok1 || !isActive st1 then stop := true
            | .refused | .pass =>
            match bulkOpenMarkup st chunk i with
            | some (st', evs', j) =>
              let (ok', acc') := deliverStep collect chunk sink acc
                (stepEventsOfFlush evs')
              st := st'
              acc := acc'
              i := j
              if !ok' || !isActive st' then stop := true
            | none =>
            match bulkCharRef st chunk i with
            | some (st', j) =>
              st := st'
              i := j
            | none =>
              let run := scanTextRun st chunk i
              if run.len > 0 then
                let s0 := noteTextStart st st.rawConsumed st.line st.column
                let allowance := s0.limits.maxTokenChars - s0.textChars
                if run.chars > allowance then
                  let failed := failCode s0 .limitToken "limitToken"
                    (s0.rawConsumed + allowance)
                  st := { failed with
                    failLine := s0.line,
                    failColumn := s0.column + run.chars,
                    failSet := true }
                  stop := true
                else if run.converted.isNone && s0.textPieces.isEmpty then
                  -- A literal run of this chunk with nothing carried yet: keep
                  -- the token as a borrowed span instead of copying its bytes. A
                  -- consumer that needs an owned string materializes it at the
                  -- delivery boundary, and the end of the feed takes any
                  -- unfinished span as a piece so no state outlives the chunk.
                  let sp := match s0.textSpan with
                    | some earlier => { earlier with stop := i + run.len }
                    | none => { start := i, stop := i + run.len }
                  st := { s0 with
                    textSpan := some sp,
                    mode := .text,
                    textChars := s0.textChars + run.chars,
                    column := s0.column + run.chars,
                    charIndex := s0.charIndex + run.chars,
                    rawConsumed := s0.rawConsumed + run.len }
                  i := i + run.len
                else
                  -- A continuation of a token whose earlier bytes are already
                  -- pieces, or a run the encoding had to convert: one piece for
                  -- this run, so the copy is bounded by the run.
                  let bytes :=
                    match run.converted with
                    | some converted => converted
                    | none => chunk.extract i (i + run.len)
                  st := { s0 with
                    textPieces := s0.textPieces.push bytes,
                    mode := .text,
                    textChars := s0.textChars + run.chars,
                    column := s0.column + run.chars,
                    charIndex := s0.charIndex + run.chars,
                    rawConsumed := s0.rawConsumed + run.len }
                  i := i + run.len
              else
                match chunk[i]? with
                | none => stop := true
                | some b =>
                  let off := st.rawConsumed
                  i := i + 1
                  -- The per-byte machine cannot borrow the chunk, and this byte
                  -- ends the literal run, so a pending span becomes owned bytes
                  -- before the grammar can append to the same token.
                  st := materializeTextSpan st chunk
                  st := { st with rawConsumed := st.rawConsumed + 1 }
                  match st.enc with
                  | .probing buf =>
                    let buf' := buf.push b
                    match probeAction buf' with
                    | .wait => st := { st with enc := .probing buf' }
                    | .declaration =>
                      -- The whitespace that identified the declaration is already
                      -- consumed, so the shadow resumes at the version name.
                      st := { st with enc := .declaration buf',
                                       mode := .decl .versionNameSkipWs }
                    | .signature enc skip =>
                      let (st', evs', ok) := replayProbe collect sink st enc skip buf'
                      st := st'
                      acc := pushEvents acc evs'
                      if !ok || !isActive st then stop := true
                    | .decide =>
                      let (st', evs', ok) := decideFromProbe collect sink st buf'
                      st := st'
                      acc := pushEvents acc evs'
                      if !ok || !isActive st then stop := true
                  | .declaration buf =>
                    -- Drop the stream's reference to the prefix before appending, so
                    -- the append is the sole owner of the buffer and stays linear.
                    st := { st with enc := .probing ByteArray.empty }
                    let buf' := buf.push b
                    let j := buf'.size - 1
                    -- The declaration grammar runs synchronously on the buffered
                    -- ASCII bytes, using the lexical fields the undecided encoding
                    -- leaves unused. Reusing `st` itself keeps the character buffer
                    -- uniquely owned, so this stays linear in the prefix length.
                    let hint : Option Encoding :=
                      match st.mode with
                      | .decl (.secondValue quote) =>
                        if b.toNat == quote.toNat then labelEncoding st.buf
                        else none
                      | _ => none
                    let st1 : Stream :=
                      if !st.declShadow then
                        { st with enc := .declaration buf', declShadow := false }
                      else if h : b.toNat < 0x80 then
                        match hint with
                        | some enc =>
                          -- One copy of the value buffer: the label decides the
                          -- encoding the declaration will be checked against.
                          let (s', _) :=
                            runStep 8 { st with enc := .decided enc }
                              ⟨⟨b.toNat, Or.inl (by omega)⟩, off⟩
                          { s' with enc := .declaration buf' }
                        | none =>
                          let (s', _) := runStep 8 st
                            ⟨⟨b.toNat, Or.inl (by omega)⟩, off⟩
                          { s' with enc := .declaration buf' }
                      else
                        match nonAsciiDeclFault st with
                        | some (code, reason) => failCode st code reason off
                        | none => { st with enc := .declaration buf', declShadow := false }
                    let shadowLive :=
                      st1.declShadow &&
                        (match st1.mode with
                          | .decl _ => true
                          | _ => false)
                    st := { st1 with declShadow := shadowLive }
                    if !isActive st then
                      stop := true
                    else if j ≥ 6 && buf'[j - 1]? == some 0x3F && b == 0x3E &&
                        j < st.limits.maxTokenChars then
                      let (st', evs', ok) := decideFromProbe collect sink st buf'
                      st := st'
                      acc := pushEvents acc evs'
                      if !ok || !isActive st then stop := true
                    else if buf'.size ≥ st.limits.maxTokenChars then
                      let (st', evs', ok) := decideFromProbe collect sink st buf'
                      st := st'
                      acc := pushEvents acc evs'
                      if !ok || !isActive st then stop := true
                  | .decided _ =>
                    match decodeByte st b off with
                    | .needMore st' => st := st'
                    | .progressed st' evs' =>
                      let (ok', acc') := deliverEvents collect chunk sink acc evs'
                      st := st'; acc := acc'
                      if !ok' then stop := true
                    | .failed st' evs' =>
                      let (ok', acc') := deliverEvents collect chunk sink acc evs'
                      st := st'; acc := acc'; stop := true
        return (materializeTextSpan (noteFailure st) chunk, acc)
  | _ => (s, #[])
def feedLocated (s : Stream) (chunk : ByteArray) : Stream × Array LocatedEvent :=
  feedCore true (fun _ _ => true) s chunk
def feedSink (sink : ByteArray → LocatedEvent → Bool) (s : Stream) (chunk : ByteArray) :
    Stream :=
  (feedCore false sink s chunk).1
def feed (s : Stream) (chunk : ByteArray) : Stream × Array Event :=
  let (s', evs) := feedLocated s chunk
  (s', evs.map (fun e => e.event))
def finishWithAppend (s : Stream) (ch : Char) (code : ErrorCode)
    (reason : String) (evs : Array LocatedEvent) : Stream × Array LocatedEvent :=
  match appendChar s ch s.rawConsumed with
  | (s1, some e) => (failedWith s1 e, evs)
  | (s1, none) => (failedWith s1 ⟨code, reason, s.rawConsumed⟩, evs)
def finishWithAppend2 (s : Stream) (code : ErrorCode) (reason : String)
    (evs : Array LocatedEvent) : Stream × Array LocatedEvent :=
  match appendChar s ']' s.rawConsumed with
  | (s1, some e) => (failedWith s1 e, evs)
  | (s1, none) =>
    match appendChar s1 ']' s.rawConsumed with
    | (s2, some e) => (failedWith s2 e, evs)
    | (s2, none) => (failedWith s2 ⟨code, reason, s.rawConsumed⟩, evs)
def finishDecl (s : Stream) (stage : DeclMode) (evs : Array LocatedEvent) :
    Stream × Array LocatedEvent :=
  let fail (code : ErrorCode) (reason : String) : Stream × Array LocatedEvent :=
    (failCode s code reason s.rawConsumed, evs)
  match stage with
  | .needWs1 => fail .unclosedToken "unclosedXmlDecl"
  | .versionNameSkipWs => fail .unclosedToken "unclosedXmlDecl"
  | .versionName =>
    match declNameDone s .version s.rawConsumed with
    | (s1, some e) => (failedWith s1 e, evs)
    | (s1, none) => (failCode s1 .xmlDecl "xmlDeclEquals" s1.rawConsumed, evs)
  | .versionAfterName => fail .xmlDecl "xmlDeclEquals"
  | .versionAfterEq => fail .unclosedToken "unclosedXmlDecl"
  | .versionValue _ => fail .unclosedToken "unclosedXmlDecl"
  | .versionDone _ => fail .unclosedToken "unclosedXmlDecl"
  | .versionQ sawSep =>
    if sawSep then fail .xmlDecl "xmlDeclName" else fail .xmlDecl "xmlDeclSeparator"
  | .secondName =>
    match declNameDone s .second s.rawConsumed with
    | (s1, some e) => (failedWith s1 e, evs)
    | (s1, none) => (failCode s1 .xmlDecl "xmlDeclEquals" s1.rawConsumed, evs)
  | .secondAfterName => fail .xmlDecl "xmlDeclEquals"
  | .secondAfterEq => fail .unclosedToken "unclosedXmlDecl"
  | .secondValue _ => fail .unclosedToken "unclosedXmlDecl"
  | .standaloneDone _ => fail .unclosedToken "unclosedXmlDecl"
  | .standaloneQ _ => fail .xmlDecl "xmlDeclEnd"
  | .encodingDone _ => fail .unclosedToken "unclosedXmlDecl"
  | .encodingQ sawSep =>
    if sawSep then fail .xmlDecl "xmlDeclName" else fail .xmlDecl "xmlDeclSeparator"
  | .thirdName =>
    match declNameDone s .third s.rawConsumed with
    | (s1, some e) => (failedWith s1 e, evs)
    | (s1, none) => (failCode s1 .xmlDecl "xmlDeclEquals" s1.rawConsumed, evs)
  | .thirdAfterName => fail .xmlDecl "xmlDeclEquals"
  | .thirdAfterEq => fail .unclosedToken "unclosedXmlDecl"
  | .thirdValue _ => fail .unclosedToken "unclosedXmlDecl"
  | .thirdDone => fail .unclosedToken "unclosedXmlDecl"
  | .thirdQ => (fail .xmlDecl "xmlDeclEnd")
def finishMode (s : Stream) (evs : Array LocatedEvent) : Stream × Array LocatedEvent :=
  let fail (code : ErrorCode) (reason : String) : Stream × Array LocatedEvent :=
    (failCode s code reason s.rawConsumed, evs)
  match s.mode with
  | .prologStart => fail .noElements "noRoot"
  | .epilogStart => ({ s with status := .done }, evs)
  | .contentStart => fail .noElements "unclosedElement"
  | .text => fail .noElements "unclosedElement"
  | .textBracket1 =>
    (match appendTextScalar s 0x5D s.rawConsumed with
     | (s1, some e) => (failedWith s1 e, evs)
     | (s1, none) => (failedWith s1 ⟨.noElements, "unclosedElement", s.rawConsumed⟩, evs))
  | .textBracket2 =>
    (match appendTextScalar s 0x5D s.rawConsumed with
     | (s1, some e) => (failedWith s1 e, evs)
     | (s1, none) =>
       match appendTextScalar s1 0x5D s.rawConsumed with
       | (s2, some e) => (failedWith s2 e, evs)
       | (s2, none) =>
         (failedWith s2 ⟨.noElements, "unclosedElement", s.rawConsumed⟩, evs))
  | .markup =>
    match s.phase with
    | .epilog => fail .junkAfterDocElement "junkAfterRoot"
    | _ => fail .invalidToken "unexpectedEnd"
  | .bang =>
    match s.phase with
    | .epilog => fail .junkAfterDocElement "junkAfterRoot"
    | _ => (failedWith s (unknownMarkupError s), evs)
  | .bangDash =>
    match s.phase with
    | .epilog => fail .junkAfterDocElement "junkAfterRoot"
    | _ => (failedWith s (unknownMarkupError s), evs)
  | .bangCdata _ => (failedWith s (unknownMarkupError s), evs)
  | .bangDoctype _ => (failedWith s (unknownMarkupError s), evs)
  | .endName => fail .invalidToken "expectedName"
  | .endNameRest => fail .unclosedToken "unclosedEndTag"
  | .endClose _ => fail .unclosedToken "unclosedEndTag"
  | .piTarget => fail .invalidToken "expectedName"
  | .piTargetRest =>
    let target := bufferString s.buf
    if target == "xml" then
      if s.phase == .prolog && s.markupIndex == 0 then
        fail .unclosedToken "unclosedXmlDecl"
      else fail .misplacedXmlPi "misplacedXmlDecl"
    else if target.toLower == "xml" then fail .invalidToken "reservedPiTarget"
    else fail .unclosedToken "unclosedPi"
  | .piAfterTarget _ => fail .unclosedToken "unclosedPi"
  | .piSkipWs _ => fail .unclosedToken "unclosedPi"
  | .piQInit _ => fail .invalidToken "piSyntax"
  | .piData _ => fail .unclosedToken "unclosedPi"
  | .piQ _ => finishWithAppend s '?' .unclosedToken "unclosedPi" evs
  | .comment => fail .unclosedToken "unclosedComment"
  | .commentDash1 => finishWithAppend s '-' .unclosedToken "unclosedComment" evs
  | .commentDash2 => fail .invalidToken "doubleHyphenInComment"
  | .cdata => fail .unclosedCdataSection "unclosedCdata"
  | .cdataBracket1 => finishWithAppend s ']' .unclosedCdataSection "unclosedCdata" evs
  | .cdataBracket2 =>
    finishWithAppend2 s .unclosedCdataSection "unclosedCdata" evs
  | .startNameRest => fail .unclosedToken "unclosedStartTag"
  | .startAfterName => fail .unclosedToken "unclosedStartTag"
  | .startSlash => fail .invalidToken "badEmptyTag"
  | .attrNameRest => fail .invalidToken "missingEquals"
  | .attrAfterName => fail .invalidToken "missingEquals"
  | .attrAfterEq => fail .unclosedToken "unclosedStartTag"
  | .attrValue _ => fail .unclosedToken "unclosedAttributeValue"
  | .refAfterAmp => fail .invalidToken "unterminatedReference"
  | .refNameRest => fail .invalidToken "unterminatedReference"
  | .refNumOptX => fail .invalidToken "malformedCharRef"
  | .refNumDigits _ _ digits _ =>
    if digits == 0 then fail .invalidToken "malformedCharRef"
    else fail .invalidToken "unterminatedCharRef"
  | .decl stage => finishDecl s stage evs
def finishGrammar (s : Stream) (evs : Array LocatedEvent) : Stream × Array LocatedEvent :=
  if s.pendingCR then
    let mapped : Char := match s.mode with
      | .attrValue _ => ' '
      | _ => '\n'
    let appended : Stream × Option ParseError :=
      match s.mode with
      | .text => appendTextScalar s mapped.toNat s.rawConsumed
      | _ => appendChar s mapped s.rawConsumed
    match appended with
    | (s1, some e) => (failedWith s1 e, evs)
    | (s1, none) => finishMode { s1 with pendingCR := false } evs
  else
    finishMode s evs
def finishUtf16 (collect : Bool) (sink : ByteArray → LocatedEvent → Bool)
    (s : Stream) (evs : Array LocatedEvent) (bigEndian : Bool) :
    Stream × Array LocatedEvent :=
  match s.pending.size with
  | 0 => finishGrammar s evs
  | 1 => (failHere s .partialChar "oddUtf16Length" s.pendingOffset, evs)
  | 2 =>
    match s.pending[0]?, s.pending[1]? with
    | some b0, some b1 =>
      let u := utf16Unit bigEndian b0 b1
      if u < 0xD800 then
        match decodeUtf16One s.pending bigEndian 0 with
        | .ok (sc, _) =>
          let (s1, evs1) := stepChar { s with pending := ByteArray.empty }
            ⟨sc, s.pendingOffset⟩
          let (ok, acc) := deliverEvents collect ByteArray.empty sink evs evs1
          if ok && isActive s1 then finishGrammar s1 acc else (s1, acc)
        | .error e =>
          (failHere s e.reason.code e.reason.name (s.pendingOffset + e.offset), evs)
      else (failHere s .invalidToken "unpairedSurrogate" s.pendingOffset, evs)
    | _, _ => (failHere s .partialChar "oddUtf16Length" s.pendingOffset, evs)
  | _ => (failHere s .partialChar "oddUtf16Length" s.pendingOffset, evs)
def finishDecoded (collect : Bool) (sink : ByteArray → LocatedEvent → Bool)
    (s : Stream) (evs : Array LocatedEvent) : Stream × Array LocatedEvent :=
  match s.enc with
  | .decided enc =>
    match enc with
    | .utf8 =>
      if s.pending.isEmpty then finishGrammar s evs
      else
        match decodeUtf8One s.pending 0 with
        | .ok (sc, _) =>
          let (s1, evs1) := stepChar { s with pending := ByteArray.empty }
            ⟨sc, s.pendingOffset⟩
          let (ok, acc) := deliverEvents collect ByteArray.empty sink evs evs1
          if ok && isActive s1 then finishGrammar s1 acc else (s1, acc)
        | .error e =>
          (failHere s e.reason.code e.reason.name (s.pendingOffset + e.offset), evs)
    | .utf16le => finishUtf16 collect sink s evs false
    | .utf16be => finishUtf16 collect sink s evs true
    | .latin1 => finishGrammar s evs
    | .ascii => finishGrammar s evs
  | _ => finishGrammar s evs
def finishCore (collect : Bool) (sink : ByteArray → LocatedEvent → Bool)
    (s : Stream) : Stream × Array LocatedEvent :=
  match s.status with
  | .active =>
    if !s.tagCarry.isEmpty then
      -- A start tag that never completed: settle its bytes through the
      -- per-byte machine, then finish from there so the EOF fault is the one
      -- those bytes determine.
      let base := s.rawConsumed
      let carried := s.tagCarry
      let settled := { s with
        tagCarry := ByteArray.empty, tagCarryCopied := 0,
        rawConsumed := s.rawConsumed + carried.size }
      let (st1, evs1, ok1) := feedDecoded collect sink settled #[] carried base
      if !ok1 then (noteFailure st1, evs1)
      else noteFailure2 (finishDecoded collect sink st1 evs1)
    else
    match s.enc with
    | .probing buf =>
      match chooseEncoding buf s.limits.maxTokenChars with
      | .error e => (noteFailure (failedWith s e), #[])
      | .ok (enc, skip) =>
        let (s1, evs, ok) := replayProbe collect sink s enc skip buf
        if !ok then (noteFailure s1, evs)
        else
          match s1.status with
          | .active => noteFailure2 (finishDecoded collect sink s1 evs)
          | _ => (noteFailure s1, evs)
    | .declaration buf =>
      match chooseEncoding buf s.limits.maxTokenChars with
      | .error e => (noteFailure (failedWith s e), #[])
      | .ok (enc, skip) =>
        let (s1, evs, ok) := replayProbe collect sink s enc skip buf
        if !ok then (noteFailure s1, evs)
        else
          match s1.status with
          | .active => noteFailure2 (finishDecoded collect sink s1 evs)
          | _ => (noteFailure s1, evs)
    | .decided _ => noteFailure2 (finishDecoded collect sink s #[])
  | _ => (s, #[])
def finishLocated (s : Stream) : Stream × Array LocatedEvent :=
  finishCore true (fun _ _ => true) s
def finishSink (sink : ByteArray → LocatedEvent → Bool) (s : Stream) : Stream :=
  (finishCore false sink s).1
def finish (s : Stream) : Stream × Array Event :=
  let (s', evs) := finishLocated s
  (s', evs.map (fun e => e.event))
end Stream
end LexPat


