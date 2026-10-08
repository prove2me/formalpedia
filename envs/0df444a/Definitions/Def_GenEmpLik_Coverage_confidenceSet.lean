-- Prove2me | Definitions.Def_GenEmpLik_Coverage_confidenceSet
-- name    : GenEmpLik_Coverage_confidenceSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:26:31.860594+00:00
-- url     : https://prove2.me/theorems/a4b6d900-084a-41f8-8aac-fa6d2fe4acac
-- title:
--   Empirical likelihood confidence set for T_opt
-- statement:
--   The confidence set is the image of the empirical divergence ball under the optimal-value functional:
--
--   $$C_{n,\rho}=\{T_{\rm opt}(p):D_f(p\|\widehat P_n)\le\rho/n\}.$$
--
--   Here $p$ ranges over probability weights on the indexed observations. Membership of the population value in this image is the event in Theorem 3. The set uses optimal values at each feasible distribution, rather than the minimax robust program.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 12, Eq. (15)

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_empiricalOptimalValue
import Definitions.Def_GenEmpLik_Coverage_divergenceBall

namespace GenEmpLik.Coverage

/-- The image of the f-divergence ball under T_opt, p. 12, (15). -/
def confidenceSet {d n : ℕ} {Ξ : Type*}
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (f : ℝ → EReal) (ρ : ℝ) (z : Fin n → Ξ) : Set ℝ :=
  empiricalOptimalValue X ℓ z '' divergenceBall f ρ n

end GenEmpLik.Coverage


