-- Prove2me | Definitions.Def_bsv_strict_signature
-- name    : bsv_strict_signature
-- status  : Definition
-- author  : @GregoryJWard
-- created : 2026-11-26T11:39:54.292345+00:00
-- url     : https://prove2.me/theorems/baf154a3-c27d-4b1a-a559-049475342069
-- title:
--   Strict two-integer signature parser and encoder
-- statement:
--   A model of a strict parser for a signature written as a pair of integers. Bytes are 8-bit words.
--
--   **Accepted input.** A byte string is a byte `0x30`, a length byte equal to the number of bytes that follow, then two INTEGER fields and nothing else. An INTEGER field is a byte `0x02`, a length byte $n$ with $1 \le n \le 33$, and $n$ content bytes $v_0, \dots, v_{n-1}$ such that:
--
--   1. the top bit of $v_0$ is clear;
--   2. if $v_0 = 0$ and $n \ge 2$, the top bit of $v_1$ is set;
--   3. if $n = 33$, then $v_0 = 0$.
--
--   The value of the field is its content (without $v_0$ when $n = 33$), padded on the left with zero bytes to 32 bytes, so both returned values are 32 bytes long. The parser `strictSig` returns the pair $(r, s)$ of values.
--
--   **Encoder.** For a byte string $x$ let $c(x)$ be $x$ with all leading zero bytes removed, replaced by the single byte $0$ if nothing remains, and with one zero byte put in front if the first remaining byte has its top bit set. `encInt` writes `0x02`, the length of $c(x)$ modulo 256, and $c(x)$. `encSig` writes `0x30`, the length modulo 256 of the two encoded fields, and the two fields.
--
--   Neither $r$ nor $s$ is checked to be non-zero or below a curve order (zero is accepted), and no claim is made that the encoder conforms to the DER standard. The file ends with examples showing inputs that are accepted and refused.
-- source:
--   Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan, BSV Lean proofs (Apache-2.0). https://github.com/codenlighten/bsv-lean-proofs

/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
Source: https://github.com/codenlighten/bsv-lean-proofs (41c4bfd), Apache-2.0.
-/

namespace Bsv.StrictSignature

abbrev Byte := BitVec 8

/-- A leading zero byte followed by a byte whose top bit is clear, so the
zero is not needed. -/
def padded (v0 : Byte) : List Byte → Bool
  | [] => false
  | v1 :: _ => v0 == 0#8 && !v1.msb

/-- Reads one INTEGER: the value left-padded to 32 bytes, and the unread
remainder. -/
def strictInt : List Byte → Option (List Byte × List Byte)
  | tag :: len :: rest =>
    let n := len.toNat
    if tag != 0x02#8 || n == 0 || decide (n > 33) || decide (rest.length < n) then none else
    match rest.take n with
    | [] => none
    | v0 :: vt =>
      -- negative, or padded
      if v0.msb || padded v0 vt then none else
      -- thirty-three bytes only with a leading zero
      if vt.length == 32 && v0 != 0#8 then none else
      let value := if vt.length == 32 then vt else v0 :: vt
      some (List.replicate (32 - value.length) 0#8 ++ value, rest.drop n)
  | _ => none

/-- Reads a sequence of two INTEGERs, with nothing left over, and returns the
pair `(r, s)` of 32-byte values. Neither is checked to be non-zero or below a
curve order. -/
def strictSig : List Byte → Option (List Byte × List Byte)
  | seq :: len :: body =>
    if seq != 0x30#8 || len.toNat != body.length then none else
    match strictInt body with
    | none => none
    | some (r, body) =>
      match strictInt body with
      | none => none
      | some (s, body) => if body.isEmpty then some (r, s) else none
  | _ => none

/-- The canonical content bytes for a big-endian value: leading zeros removed,
one zero byte kept for zero or put back when the top bit is set. -/
def canon (out : List Byte) : List Byte :=
  match out.dropWhile (· == 0#8) with
  | [] => [0#8]
  | h :: t => if h.msb then 0#8 :: h :: t else h :: t

/-- The canonical INTEGER encoding used in this model. -/
def encInt (out : List Byte) : List Byte :=
  0x02#8 :: BitVec.ofNat 8 (canon out).length :: canon out

def encSig (r s : List Byte) : List Byte :=
  0x30#8 :: BitVec.ofNat 8 (encInt r ++ encInt s).length :: (encInt r ++ encInt s)

/-! ## Examples: the parser does accept, and refuses the known bad shapes -/

/-- r = 1, s = 1 is accepted. -/
example : (strictSig [0x30, 6, 2, 1, 1, 2, 1, 1]).isSome = true := by decide

/-- A zero-padded 1 is refused. -/
example : strictInt [2, 2, 0, 1] = none := by decide

/-- A negative INTEGER is refused. -/
example : strictInt [2, 1, 0x80] = none := by decide

/-- 0x80 with the zero it needs is accepted. -/
example : (strictInt [2, 2, 0, 0x80]).isSome = true := by decide

/-- Thirty-three bytes whose first byte is not zero are refused. -/
example : strictInt (2 :: 33 :: 1 :: List.replicate 32 0xff) = none := by decide

/-- Trailing bytes are refused. -/
example : strictSig [0x30, 6, 2, 1, 1, 2, 1, 1, 0] = none := by decide

/-- r = 0, s = 0 is accepted: no non-zero check is modelled. -/
example : (strictSig [0x30, 6, 2, 1, 0, 2, 1, 0]).isSome = true := by decide

end Bsv.StrictSignature


