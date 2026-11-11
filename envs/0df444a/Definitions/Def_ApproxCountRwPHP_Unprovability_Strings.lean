-- Prove2me | Definitions.Def_ApproxCountRwPHP_Unprovability_Strings
-- name    : ApproxCountRwPHP_Unprovability_Strings
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:55:17.795315+00:00
-- url     : https://prove2.me/theorems/fb28614d-65b6-44f5-83df-7f7b488da8a9
-- title:
--   Binary strings and numerical encodings
-- statement:
--   A binary string is a finite list of Boolean bits, stored most significant first. Its length is its list length. Leading zeroes are retained, while numerical decoding forgets them. The shortest binary representation of zero is the empty string. Fixed-width encoding keeps exactly the requested number of low bits, padding with leading zeroes.
--
--   $$\operatorname{number}(b_1\cdots b_n)=\sum_{i=1}^n b_i2^{n-i}.$$
--
--   Unary strings contain only ones. These conventions keep strings distinct from their numerical values and supply the common encoding layer for arithmetic and circuit descriptions.
--
--   Natural-number variables use only canonical shortest binary numerals, recognized by isNumeral; this restriction does not apply to arbitrary string variables.
-- source:
--   Oliver Korten, Jiatu Li, Igor Oliveira, Hanlin Ren, STOC 2027 submission #1023 (October 2026), §2.1–2.2, printed p. 13–14, PDF p. 15–16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1023.pdf#page=15–16

import Mathlib

namespace ApproxCountRwPHP.Unprovability

/-! Binary strings in §2.1–2.2 (printed 13–14 / PDF 15–16).
Bits are stored most significant first. Leading zeroes are retained in strings;
`number` forgets them. `bits n w` keeps exactly the low `w` bits of `n`.
Numbers use the shortest representation, with zero represented by the empty string.
These are encodings, not an identification of strings with natural numbers. -/
abbrev BitString := List Bool

def number (x : BitString) : ℕ := x.foldl (fun n b => 2 * n + b.toNat) 0

def bits (n w : ℕ) : BitString :=
  ((List.range w).reverse).map (fun i => n.testBit i)

def numeral (n : ℕ) : BitString :=
  (Nat.digits 2 n).reverse.map (fun d => d != 0)

/-- Natural-number variables use the unique shortest encoding. Arbitrary
strings (including leading zeroes) remain available elsewhere in the language. -/
def isNumeral (x : BitString) : Bool := x == numeral (number x)

def unary (n : ℕ) : BitString := List.replicate n true

def truth (p : Bool) : BitString := if p then [true] else []

/-- Length-limited recursion returns a prefix if its proposed answer is too long. -/
def boundString (answer bound : BitString) : BitString := answer.take bound.length

end ApproxCountRwPHP.Unprovability


