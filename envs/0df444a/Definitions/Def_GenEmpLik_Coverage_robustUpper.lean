-- Prove2me | Definitions.Def_GenEmpLik_Coverage_robustUpper
-- name    : GenEmpLik_Coverage_robustUpper
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:26:49.768813+00:00
-- url     : https://prove2.me/theorems/d9d933be-f7f3-40c9-b02c-f92268243ba3
-- title:
--   Upper endpoint of the optimal-value image
-- statement:
--   The upper endpoint associated with the empirical divergence ball is
--
--   $$U_{n,\rho}=\sup_{p:D_f(p\|\widehat P_n)\le\rho/n}T_{\rm opt}(p).$$
--
--   It is the upper endpoint of the image of the ball under $T_{\rm opt}$. The paper uses this quantity in the one-sided limit and the expansion after (37).
--
--   **Formalization Note** This is $\sup_p\inf_x$; the separate robust optimization program is $\inf_x\sup_p$.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 37, Appendix B.4, display after (37)

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_empiricalOptimalValue
import Definitions.Def_GenEmpLik_Coverage_divergenceBall

namespace GenEmpLik.Coverage

/-- The upper endpoint of the image of the divergence ball under T_opt. -/
noncomputable def robustUpper {d n : ℕ} {Ξ : Type*}
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (f : ℝ → EReal) (ρ : ℝ) (z : Fin n → Ξ) : ℝ :=
  sSup (empiricalOptimalValue X ℓ z '' divergenceBall f ρ n)

end GenEmpLik.Coverage


