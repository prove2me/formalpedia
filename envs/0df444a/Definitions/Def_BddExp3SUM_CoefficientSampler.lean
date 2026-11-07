-- Prove2me | Definitions.Def_BddExp3SUM_CoefficientSampler
-- name    : BddExp3SUM_CoefficientSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:32.221982+00:00
-- url     : https://prove2.me/theorems/ec3d72b1-8d70-4d06-91ee-c969b0cdb687
-- title:
--   Rejection sampling of coefficients in $\mathbb Z_M$ from $C$ fair bits
-- statement:
--   An attempt is a string of $C$ bits, read as the number $\sum_i b_i2^i$. Given a sequence of attempts, the accepted values are those below $M$, in order, as elements of $\mathbb Z_M$. The first $t$ accepted values are the coefficients, if there are that many.
--
--   This is the procedure by which the paper generates uniform coefficients from fair bits, and it makes the random-bit cost explicit.
--
--   **Formalization Note** A subinstance's sampler draws a fixed number of attempts in advance, and `firstCoeffs` returns `none` if fewer than $t$ are accepted.
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), §6, p.7

import Mathlib

namespace BddExp3SUM

/-!
# Rejection sampling of coefficients in `Z_M` from `C` fair bits

Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission (manuscript sha256 19546c9a…), §6, p.7: "uniform
coefficients in Z_M are generated from C fair bits by rejecting values at least M".

**Formalization Note.** An attempt is a function `Fin C → Bool`, read as the number
`∑ i, b_i 2^i`. An execution draws a fixed sequence of attempts, and `accepted` lists the values below
`M`, in order, as elements of `ZMod M`. The first `t` accepted values are the coefficients; the
subinstance aborts if fewer than `t` are accepted.
-/

/-- The number written by `C` bits. -/
def attemptValue {C : ℕ} (b : Fin C → Bool) : ℕ := ∑ i, if b i then 2 ^ i.val else 0

/-- The accepted values of a sequence of attempts, in order. -/
def accepted (M : ℕ) {C T : ℕ} (a : Fin T → Fin C → Bool) : List (ZMod M) :=
  ((List.ofFn a).filter fun b => decide (attemptValue b < M)).map fun b => (attemptValue b : ZMod M)

/-- The first `t` entries of a list, if it has that many. -/
def firstCoeffs {β : Type*} (l : List β) (t : ℕ) : Option (Fin t → β) :=
  if h : t ≤ l.length then some fun i => l[i.val]'(lt_of_lt_of_le i.isLt h) else none

end BddExp3SUM


