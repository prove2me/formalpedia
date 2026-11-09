-- Prove2me | Definitions.Def_CubeSampling_olsWorstRisk
-- name    : CubeSampling_olsWorstRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:18:56.3602+00:00
-- url     : https://prove2.me/theorems/bc9d91f8-b009-4fc2-ab2a-d3b5de9bd611
-- title:
--   Worst-subspace risk of ordinary least squares
-- statement:
--   The worst-subspace risk of OLS is
--   $$
--   \sup_{V \subseteq P_{d,k},\ \dim V = m}\ \sup_{\hat\theta \text{ OLS rule}}\ \sup_{\theta \in \mathbb R^m} Q_{1-\delta,\theta}\bigl(\|\hat\theta - \theta\|_2^2\bigr),
--   $$
--   where the middle supremum runs over the measurable OLS rules for $V$. It measures the guarantee of Theorem 1.5 that its upper bound "is attained by ordinary least squares".
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Theorem 1.5, p.4

import Mathlib
import Definitions.Def_CubeSampling_riskQuantile
import Definitions.Def_CubeSampling_IsOrthonormalFamily
import Definitions.Def_CubeSampling_lowDeg
import Definitions.Def_CubeSampling_IsOLSRule
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSampling

/-- The worst-subspace risk of ordinary least squares (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Theorem 1.5, p.4: "attained by
ordinary least squares"): the supremum over `m`-dimensional `V ⊆ P_{d,k}` (orthonormal families
`Φ`), over measurable OLS rules and over `θ ∈ ℝ^m` of `Q_{1−δ,θ}(‖θ̂_OLS − θ‖₂²)`. -/
noncomputable def olsWorstRisk (d k m : ℕ) (σ : ℝ) (n : ℕ) (δ : ℝ) : ℝ≥0∞ :=
  ⨆ (Φ : Fin m → Cube d → ℝ) (_ : IsOrthonormalFamily Φ ∧ ∀ j, Φ j ∈ lowDeg d k),
    ⨆ (est : (Fin n → Cube d × ℝ) × unitInterval → (Fin m → ℝ))
      (_ : Measurable est ∧ IsOLSRule Φ n est),
      ⨆ θ : Fin m → ℝ, riskQuantile Φ σ n δ est θ

end CubeSampling


