-- Prove2me | Definitions.Def_burau_cf_pair
-- name    : burau_cf_pair
-- status  : Definition
-- author  : @lt9
-- created : 2026-09-30T22:22:08.41402+00:00
-- url     : https://prove2.me/theorems/eb009a35-dccb-4cb1-970f-cbe995145a6a
-- title:
--   The pair-level Euclidean descent (continued-fraction recursion cfPair)
-- statement:
--   **The pair-level (subtractive) Euclidean descent of a rational.**
--
--   For integers $a,b$ the recursion
--   $$ \mathtt{cfPair}(a,b)=\begin{cases}[] & a=0,\\ \dfrac{b}{a} :: \mathtt{cfPair}\bigl(b\bmod a,\ -a\bigr) & a\neq 0\end{cases} $$
--   records the quotient list of the descent on $\mathrm{SL}(2,\mathbb Z)$ matrices that sends a matrix $M$
--   with nonzero $M_{00}$ to $(M\cdot T^{-n})\cdot S$ with $n=M_{01}/M_{00}$. Termination follows from
--   $|b\bmod a|<|a|$; the companion lemmas give the recursion equation, the terminating case, and the two
--   negated-divisor identities. This integer recursion is the combinatorial skeleton of the section
--   $\rho$ of the reduced braid quotient $Q\cong\mathrm{SL}(2,\mathbb Z)$ used in the three-strand Burau
--   faithfulness reduction, and it is the object whose comparison with the *standard* descent
--   (`burau_std_cf`) encodes the continued-fraction reciprocity on which the $S$-rule depends.
-- source:
--   Euclidean algorithm in SL(2,Z); cf. C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3; J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82 (1974), §3.3.

import Mathlib

set_option autoImplicit false

namespace BurauNC

/-- The descent restricted to the first row: the quotient list of the Euclidean algorithm on `b/a`. -/
noncomputable def cfPair (a b : ℤ) : List ℤ :=
  if h : a = 0 then [] else b / a :: cfPair (b % a) (-a)
termination_by a.natAbs
decreasing_by
  have h1 : 0 ≤ b % a := Int.emod_nonneg b h
  have h2 : b % a < |a| := Int.emod_lt_abs b h
  have h3 : |b % a| < |a| := by rwa [abs_of_nonneg h1]
  rw [Int.natAbs_lt_iff_sq_lt]
  exact sq_lt_sq.mpr h3

theorem cfPair_cons (a b : ℤ) (h : a ≠ 0) : cfPair a b = b / a :: cfPair (b % a) (-a) := by
  rw [cfPair.eq_def]
  exact dif_neg h

theorem cfPair_zero (b : ℤ) : cfPair 0 b = [] := by
  rw [cfPair.eq_def]
  exact dif_pos rfl

/-- Negating the *divisor* negates the Euclidean quotient … -/
theorem ediv_neg_divisor (a b : ℤ) : b / (-a) = -(b / a) := Int.ediv_neg b a

/-- … while the Euclidean remainder is unchanged. This is the structural basis of the continued
fraction reversal: the two descents `(a,b) ↦ (b % a, -a)` and `(b,-a) ↦ (b % a, -b)` share the same
remainders with opposite quotient signs. -/
theorem emod_neg_divisor (a b : ℤ) : b % (-a) = b % a := Int.emod_neg b a

end BurauNC


