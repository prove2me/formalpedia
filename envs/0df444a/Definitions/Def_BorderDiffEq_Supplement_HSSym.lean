-- Prove2me | Definitions.Def_BorderDiffEq_Supplement_HSSym
-- name    : BorderDiffEq_Supplement_HSSym
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:53:00.246505+00:00
-- url     : https://prove2.me/theorems/bcfd253b-87a3-46cc-ba0b-282bb347990c
-- title:
--   Alphabet and binary codes for hitting-set constructions
-- statement:
--   Explicit hitting sets are produced by machines that read their parameters and write points. The alphabet has five symbols: the binary digits $0,1$, a minus sign, a field separator and a point separator.
--
--   1. A list of natural numbers is written in binary, each number followed by a field separator.
--   2. An output is decoded into a list of points of $\mathbb Q^n$: it is cut at the point separators, empty pieces are dropped, and in each piece the $i$-th coordinate is $a/b$, where the integer $a$ (optional minus sign, then binary digits) is the $2i$-th field and the natural number $b$ is the $(2i+1)$-th field; a missing field reads as $0$ and $a/0=0$.
--
--   Decoding is a fixed total function that builds each coordinate from its own digits, so the work of a construction is done by the machine writing the output.
--
--   Machines read and write bits. Every symbol is written as a block of three bits; a bit string is read back three bits at a time (an incomplete final block is ignored, a block coding no symbol reads as the point separator). The input of a construction is the bit code of its list of parameters, and its output is the list of points written by the bit string it produces.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Theorems 2.2 and 2.6, pp.7 and 9 ("explicit hitting set … constructed in time")

import Mathlib

namespace BorderDiffEq.Supplement

/-- **The alphabet in which hitting-set constructions read their parameters and write their
points** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits
via Differential Equations*, manuscript (STOC 2027 submission), Theorems 2.2 and 2.6, pp.7 and 9:
"an explicit hitting set ... which can be constructed in time ..."). The symbols are the two
binary digits, a minus sign, a field separator and a point separator.

**Formalization Note.** Parameters (natural numbers) are written in binary
(`Computability.encodeNat`), each followed by `sep` (`encodeNats`). The output of a construction
is decoded by `decodePts n`: the output is cut at every `pt`, empty pieces are dropped, and each
piece is one point of `ℚⁿ`, whose `i`-th coordinate is `a / b` for the integer `a` written in the
`2i`-th field (an optional leading `neg`, then binary digits) and the natural number `b` written in
the `(2i+1)`-th field (fields are separated by `sep`; a missing field reads as `0`, and Lean's
`a / 0 = 0`). Decoding is a fixed total function that produces each coordinate from its own
digits, so the machine that writes the output does all the work of the construction.

Machines read and write bits: every symbol is written as a block of three bits (`toBits`), and
`ofBits` reads a bit string back three bits at a time (an incomplete final block is ignored).
`encodeInput` is the bit code of a list of parameters and `decodeOutput n` the list of points
written by a bit string. -/
inductive HSSym : Type where
  | b0
  | b1
  | neg
  | sep
  | pt
  deriving DecidableEq

namespace HSSym

/-- Binary code of a list of natural numbers, each number followed by `sep`. -/
def encodeNats (l : List ℕ) : List HSSym :=
  l.flatMap fun m => (Computability.encodeNat m).map (fun b => if b then b1 else b0) ++ [sep]

/-- The natural number written by a field (`b1` is the digit 1, every other symbol the digit 0). -/
def decodeNatField (l : List HSSym) : ℕ :=
  Computability.decodeNat (l.map fun c => decide (c = b1))

/-- The integer written by a field: an optional leading `neg`, then binary digits. -/
def decodeIntField : List HSSym → ℤ
  | neg :: r => -(decodeNatField r : ℤ)
  | r => (decodeNatField r : ℤ)

/-- The point of `ℚⁿ` written by one piece of the output. -/
def decodePoint (n : ℕ) (l : List HSSym) : Fin n → ℚ := fun i =>
  ((decodeIntField ((l.splitOn sep).getD (2 * i) []) : ℚ)) /
    ((decodeNatField ((l.splitOn sep).getD (2 * i + 1) []) : ℚ))

/-- The list of points of `ℚⁿ` written by an output. -/
def decodePts (n : ℕ) (out : List HSSym) : List (Fin n → ℚ) :=
  ((out.splitOn pt).filter fun l => !l.isEmpty).map (decodePoint n)

/-- The three-bit code of a symbol. -/
def toBits : HSSym → List Bool
  | b0 => [false, false, false]
  | b1 => [false, false, true]
  | neg => [false, true, false]
  | sep => [false, true, true]
  | pt => [true, false, false]

/-- The symbol of a three-bit block (blocks that code no symbol read as `pt`). -/
def ofBits3 : Bool → Bool → Bool → HSSym
  | false, false, false => b0
  | false, false, true => b1
  | false, true, false => neg
  | false, true, true => sep
  | _, _, _ => pt

/-- Read a bit string three bits at a time. -/
def ofBits : List Bool → List HSSym
  | a :: b :: c :: r => ofBits3 a b c :: ofBits r
  | _ => []

/-- The bit code of a list of natural numbers (the input of a construction). -/
def encodeInput (l : List ℕ) : List Bool := (encodeNats l).flatMap toBits

/-- The points of `ℚⁿ` written by a bit string (the output of a construction). -/
def decodeOutput (n : ℕ) (out : List Bool) : List (Fin n → ℚ) := decodePts n (ofBits out)

end HSSym

end BorderDiffEq.Supplement


