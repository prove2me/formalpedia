-- Prove2me | Definitions.Def_JRPHard_Shor_Setting
-- name    : JRPHard_Shor_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T12:38:32.376054+00:00
-- url     : https://prove2.me/theorems/f5cac4ca-ffae-4410-b860-e75aca45f722
-- title:
--   Appendix scaling and interval endpoints
-- statement:
--   Given a positive bit parameter $B$ and indexed integers $a_1,\ldots,a_n$, define the real scaling factor, half-total, and scaled exponents by
--   $$\lambda=\frac{3B}{2^B},\qquad A=\frac12\sum_{i=1}^n a_i,\qquad b_i=\lambda a_i.$$
--   The real interval endpoints are
--   $$L=2^{\lambda(A-1/2)},\qquad U=2^{\lambda(A+1/2)}.$$
--   These definitions are the numerical data of the Appendix reduction. The half-total uses real division, and every exponent involving $\lambda$ is a real exponent.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 16–17, Appendix, scaling and endpoints

import Mathlib
import Definitions.Def_JRPHard_Shor_DecisionProblems

namespace JRPHard.Shor

open Finset

/-- The Appendix's scaling factor λ = 3B / 2^B. -/
noncomputable def scale (B : ℕ) : ℝ := 3 * (B : ℝ) / (2 : ℝ) ^ B

/-- A = (Σ aᵢ)/2, with division in the reals. -/
noncomputable def halfSum {n : ℕ} (a : Fin n → ℕ) : ℝ :=
  ((∑ i, a i : ℕ) : ℝ) / 2

/-- The exponent bᵢ = λaᵢ. -/
noncomputable def expo {n : ℕ} (B : ℕ) (a : Fin n → ℕ) (i : Fin n) : ℝ :=
  scale B * (a i : ℝ)

/-- The real lower endpoint L. -/
noncomputable def lowL {n : ℕ} (B : ℕ) (a : Fin n → ℕ) : ℝ :=
  (2 : ℝ) ^ (scale B * (halfSum a - 1 / 2))

/-- The real upper endpoint U. -/
noncomputable def highU {n : ℕ} (B : ℕ) (a : Fin n → ℕ) : ℝ :=
  (2 : ℝ) ^ (scale B * (halfSum a + 1 / 2))

end JRPHard.Shor


