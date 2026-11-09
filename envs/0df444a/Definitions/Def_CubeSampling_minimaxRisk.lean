-- Prove2me | Definitions.Def_CubeSampling_minimaxRisk
-- name    : CubeSampling_minimaxRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:18:55.682522+00:00
-- url     : https://prove2.me/theorems/b8e42d52-14d4-410d-bd11-b9df274564c1
-- title:
--   Supplied-model minimax risk $R^*_{n,\delta}(V)$
-- statement:
--   For an $m$-dimensional model $V$ with orthonormal basis $\Phi$, noise level $\sigma$, sample size $n$ and confidence $\delta$,
--   $$
--   R^*_{n,\delta}(V) = \inf_{\hat\theta_V}\ \sup_{\theta \in \mathbb R^m} Q_{1-\delta,\theta}\bigl(\|\hat\theta_V - \theta\|_2^2\bigr).
--   $$
--   The infimum is over all estimators, with no computational restriction.
--
--   **Formalization Note** The infimum runs over all measurable randomized estimators: measurable maps of the data and of an independent uniform variable $U$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, p.3

import Mathlib
import Definitions.Def_CubeSampling_riskQuantile
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSampling

/-- The supplied-model minimax risk `R*_{n,δ}(V) = inf_θ̂ sup_{θ ∈ ℝ^m} Q_{1−δ,θ}(‖θ̂ − θ‖₂²)` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1,
p.3), for the subspace `V` with orthonormal basis `Φ`, noise level `σ` and `n` samples.

**Formalization Note** The infimum runs over all measurable (randomized) estimators: measurable
maps of the data and of an independent `U ~ Uniform[0, 1]`. There are no computational
restrictions. -/
noncomputable def minimaxRisk {d m : ℕ} (Φ : Fin m → Cube d → ℝ) (σ : ℝ) (n : ℕ) (δ : ℝ) : ℝ≥0∞ :=
  ⨅ (est : (Fin n → Cube d × ℝ) × unitInterval → (Fin m → ℝ)) (_ : Measurable est),
    ⨆ θ : Fin m → ℝ, riskQuantile Φ σ n δ est θ

end CubeSampling


