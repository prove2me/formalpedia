-- Prove2me | Definitions.Def_GenEmpLik_Coverage_empiricalOptimalValue
-- name    : GenEmpLik_Coverage_empiricalOptimalValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:03:58.929978+00:00
-- url     : https://prove2.me/theorems/16d75488-3e9e-4b57-a32a-fe13fba6ad7b
-- title:
--   Optimal value under empirical weights
-- statement:
--   For observations $z_0,\ldots,z_{n-1}$ and probability weights $p_0,\ldots,p_{n-1}$, the optimal value under the weighted empirical law is
--
--   $$T_{\rm opt}(p)=\inf_{x\in\mathcal X}\sum_{i=0}^{n-1}p_i\ell(x;z_i).$$
--
--   This representation keeps repeated observations as separate sample indices. Under the theorem's assumptions, the infimum is a genuine finite minimum for every probability weight vector.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 12, Eq. (15) and the definition of T_opt

import Mathlib

namespace GenEmpLik.Coverage

/-- T_opt of the weighted empirical distribution on the n indexed observations. -/
noncomputable def empiricalOptimalValue {d n : ℕ} {Ξ : Type*}
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (z : Fin n → Ξ) (p : Fin n → ℝ) : ℝ :=
  sInf ((fun x => ∑ i, p i * ℓ x (z i)) '' X)

end GenEmpLik.Coverage


