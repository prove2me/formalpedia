-- Prove2me | Definitions.Def_eulerMascheroni_factorialQuotient
-- name    : eulerMascheroni_factorialQuotient
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-11T13:16:03.227533+00:00
-- url     : https://prove2.me/theorems/e8aa6c99-f9df-4a49-818b-f2e52016742e
-- title:
--   Factorial quotient coefficients and their common-denominator condition
-- statement:
--   For a real parameter $a$, define
--
--   $$q_n(a)=\frac{a-\sum_{k<n}(-1)^k k!}{n!}.$$
--
--   The predicate $\mathrm{ExponentialDenominators}(a)$ asserts that there is $C\ge1$ such that, for each $n$, one positive integer $D_n\le C^{n+1}$ makes all $D_nq_k(a)$ with $k\le n$ algebraic integers. These are the Borel coefficients of the quotient by $1-w$ of $a-\sum_{n\ge0}(-1)^n n!w^{n+1}$.
-- source:
--   Fischler–Rivoal, Relations between values of arithmetic Gevrey series, and applications to values of the Gamma function, JNT 261 (2024), 36–54, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Conjecture 2, p. 4; coefficients derived by multiplication with the geometric series. The denominator predicate is the standard G-function common-denominator condition.

import Definitions.Def_eulerMascheroni_gompertz

noncomputable section
namespace EulerMascheroni.Arithmetic

/-- Taylor coefficients of the Borel transform of the divided Euler factorial tail. -/
def quotientCoeff (a : ℝ) (n : ℕ) : ℝ :=
  (a - ∑ k ∈ Finset.range n, (-1 : ℝ)^k * (k.factorial : ℝ)) / (n.factorial : ℝ)

/-- The common-denominator condition in the definition of a G-function.
The exponent n+1 includes the initial coefficient. -/
def ExponentialDenominators (a : ℝ) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, ∃ D : ℕ, 0 < D ∧
    (D : ℝ) ≤ C^(n+1) ∧ ∀ k : ℕ, k ≤ n →
      IsIntegral ℤ ((D : ℝ) * quotientCoeff a k)

end EulerMascheroni.Arithmetic


