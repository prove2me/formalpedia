-- Prove2me | Definitions.Def_burau_std_cf
-- name    : burau_std_cf
-- status  : Definition
-- author  : @lt9
-- created : 2026-09-30T21:25:35.453976+00:00
-- url     : https://prove2.me/theorems/da4c37aa-f38a-4d5a-959a-16779d304a7d
-- title:
--   Standard Euclidean continued fraction of a rational (with canonical form)
-- statement:
--   **The standard Euclidean continued fraction of a rational, together with its canonical form.**
--
--   For integers $a,b$, $\mathtt{cfStd}(a,b)$ is the quotient list produced by the *standard* (positive)
--   Euclidean descent on the rational $b/a$:
--   $$\mathtt{cfStd}(a,b)=\begin{cases}[] & a=0,\\ \dfrac{b}{a} :: \mathtt{cfStd}\bigl(b\bmod a,\ a\bigr) & a\neq 0,\end{cases}$$
--   where division and remainder are the Euclidean ones on $\mathbb Z$ (remainder of the sign of the
--   divisor). The recursion terminates because $|b\bmod a|<|a|$.
--
--   The auxiliary map $\mathtt{canon}$ puts such a list into the canonical shape of a regular continued
--   fraction by folding a final term $1$ into the preceding term: this is the normal form in which the
--   transformations $x\mapsto -1/x$ and $x\mapsto -x$ of continued fractions take their clean two- and
--   three-case forms. Both objects are the integer skeleton of the Euclidean-descent section
--   $\rho$ of $\mathrm{SL}(2,\mathbb Z)$ used in the reduction of the three-strand Burau faithfulness
--   statement to a continued-fraction identity.
-- source:
--   Standard Euclidean continued fractions; cf. A. Ya. Khinchin, *Continued Fractions* (1964), Ch. II; C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3 (Euclidean algorithm in SL(2,Z)).

import Mathlib

/-- Standard (positive) Euclidean continued fraction of the rational `b/a`: `cfStd a b = []` when
`a = 0`, and `(b/a) :: cfStd (b % a) a` otherwise. -/
noncomputable def cfStd (a b : ℤ) : List ℤ :=
  if h : a = 0 then [] else b / a :: cfStd (b % a) a
termination_by a.natAbs
decreasing_by
  have h1 : 0 ≤ b % a := Int.emod_nonneg b h
  have h2 : b % a < |a| := Int.emod_lt_abs b h
  have h3 : |b % a| < |a| := by rwa [abs_of_nonneg h1]
  rw [Int.natAbs_lt_iff_sq_lt]
  exact sq_lt_sq.mpr h3

/-- The recursion equation of `cfStd` at a nonzero first argument. -/
theorem cfStd_cons (a b : ℤ) (h : a ≠ 0) : cfStd a b = b / a :: cfStd (b % a) a := by
  rw [cfStd.eq_def]
  exact dif_neg h

/-- `cfStd` vanishes at a zero first argument. -/
theorem cfStd_zero (b : ℤ) : cfStd 0 b = [] := by
  rw [cfStd.eq_def]
  exact dif_pos rfl

/-- Normalisation of a continued-fraction list: a trailing `1` is absorbed into the previous term. -/
def canon : List ℤ → List ℤ
  | [] => []
  | [x] => [x]
  | x :: y :: l =>
      match canon (y :: l) with
      | [] => [x]
      | [z] => if z = 1 then [x + 1] else [x, z]
      | z :: zs => x :: z :: zs


