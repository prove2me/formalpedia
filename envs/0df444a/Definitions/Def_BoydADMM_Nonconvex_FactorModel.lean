-- Prove2me | Definitions.Def_BoydADMM_Nonconvex_FactorModel
-- name    : BoydADMM_Nonconvex_FactorModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:06:37.716887+00:00
-- url     : https://prove2.me/theorems/3377c3f7-f7fd-4e51-81e8-f6f600c3d258
-- title:
--   Factor-model diagonal loss and the scaled ADMM X-subproblem
-- statement:
--   Let $\Sigma$ and $X$ be real $n\times n$ matrices. For a nonnegative vector $d$, the factor-model fitting loss before eliminating the diagonal is
--
--   $$L_\Sigma(X,d)=\frac12\|X+\operatorname{diag}(d)-\Sigma\|_F^2.$$
--
--   The reduced loss is $f_\Sigma(X)=\inf_{d\ge0}L_\Sigma(X,d)$. Its proposed componentwise expression is the off-diagonal squared error plus one-sided diagonal squared error; the candidate optimizer is $d_i=(\Sigma_{ii}-X_{ii})_+$. For symmetric matrices $Z,U$ and $\rho>0$, the scaled ADMM X-subproblem minimizes $f_\Sigma(X)+(\rho/2)\|X-Z+U\|_F^2$. The file defines the entrywise candidate for that update.
--
--   These objects separate the convex X-subproblem from the nonconvex positive semidefinite rank constraint, which is imposed in the Z-update.
--
--   **Formalization Note** $f_\Sigma$ is the real infimum over all componentwise nonnegative $d$. The statements using it prove its finite explicit value. The book's diagonal branch conditions omit the iteration superscript on $Z$ and $U$; the candidate uses the current $Z$ and $U$ as the surrounding display requires. The parameter called $\rho$ in the book is `rho` in Lean.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 75, §9.1.2, factor-model loss and ADMM X-update

import Mathlib
import Definitions.Def_BoydADMM_Nonconvex_MatrixBasics

namespace BoydADMM.Nonconvex

/-- The factor-model loss before eliminating the nonnegative diagonal `d` (§9.1.2, p. 75). -/
noncomputable def factorLossWithDiag {n : ℕ} (Sigma X : SqMat n) (d : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * frobSq (X + diag d - Sigma)

/-- The book's `f(X) = inf_{d ≥ 0} (1/2) ‖X + diag(d) - Σ‖²_F`. -/
noncomputable def factorLoss {n : ℕ} (Sigma X : SqMat n) : ℝ :=
  sInf {r : ℝ | ∃ d : Fin n → ℝ, (∀ i, 0 ≤ d i) ∧
    r = factorLossWithDiag Sigma X d}

/-- The componentwise formula for `f` printed in §9.1.2. -/
noncomputable def factorLossExplicit {n : ℕ} (Sigma X : SqMat n) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j, if i ≠ j then (X i j - Sigma i j) ^ 2 else 0) +
    (1 / 2 : ℝ) * ∑ i, (max (X i i - Sigma i i) 0) ^ 2

/-- The minimizing nonnegative diagonal `d_i = (Σ_ii - X_ii)_+`. -/
def optimalDiag {n : ℕ} (Sigma X : SqMat n) : Fin n → ℝ :=
  fun i => max (Sigma i i - X i i) 0

/-- The scaled-dual `X`-subproblem objective at a step with data `Z`, `U`. -/
noncomputable def xSubproblem {n : ℕ} (Sigma Z U : SqMat n) (rho : ℝ)
    (X : SqMat n) : ℝ :=
  factorLoss Sigma X + (rho / 2) * frobSq (X - Z + U)

/-- The book's entrywise `X`-update, with the missing `k` superscripts in the
diagonal case condition restored (§9.1.2, p. 75). -/
noncomputable def xUpdate {n : ℕ} (Sigma Z U : SqMat n) (rho : ℝ) : SqMat n :=
  fun i j =>
    if i = j then
      if Sigma i i ≤ Z i i - U i i then
        (Sigma i i + rho * (Z i i - U i i)) / (1 + rho)
      else Z i i - U i i
    else (Sigma i j + rho * (Z i j - U i j)) / (1 + rho)

end BoydADMM.Nonconvex


