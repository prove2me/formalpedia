-- Prove2me | Definitions.Def_SubexpPrimes_bitsToNat
-- name    : SubexpPrimes_bitsToNat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:56:32.82211+00:00
-- url     : https://prove2.me/theorems/b09d7820-30c8-4a62-a2c2-265201b5ab7f
-- title:
--   Bit words as integers and as polynomials over $\mathbb F_2$
-- statement:
--   An $n$-bit string is read as an integer in $[0,2^n)$, most significant bit first, with leading zeros allowed. This file gives the reading, the $n$-bit string of an integer, the subword of given position and width, and the reading of a word as a polynomial over $\mathbb F_2$, most significant coefficient first.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Notation, p.13

import Mathlib

set_option autoImplicit false

namespace SubexpPrimes

/-- **Words as integers** — Gajulapalli, *Deterministic Construction of Primes in Subexponential
Time* (manuscript, sha256 6ad4d3de…), Notation, p.13: "An n-bit string is read as an integer in
[0, 2ⁿ), most significant bit first, with leading zeros allowed." -/
def bitsToNat (x : List Bool) : ℕ := x.foldl (fun acc b => 2 * acc + b.toNat) 0

/-- The `n`-bit string of `p`, most significant bit first (the low `n` bits of `p`). -/
def bitsOf (n p : ℕ) : List Bool := (List.range n).reverse.map fun i => p.testBit i

/-- The subword of `a` of width `w` starting at position `i`. Several words on one list of input
edges are read off with it. -/
def slice (a : List Bool) (i w : ℕ) : List Bool := (a.drop i).take w

/-- A word as a polynomial over `F₂`, most significant coefficient first: `b₀ … b_{k-1}` stands
for `∑ b_i X^{k-1-i}` (the convention of p.13 applied to coefficients). -/
noncomputable def polyOf (x : List Bool) : Polynomial (ZMod 2) :=
  x.foldl (fun acc b => acc * Polynomial.X + Polynomial.C (b.toNat : ZMod 2)) 0

end SubexpPrimes


