-- Prove2me | Definitions.Def_CubeSampling_riskQuantile
-- name    : CubeSampling_riskQuantile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:17:49.348481+00:00
-- url     : https://prove2.me/theorems/679f2c2f-05bc-4da4-b2e6-63f714c79a77
-- title:
--   Risk $Q_{1-\delta,\theta}(\|\hat\theta - \theta\|_2^2)$ of an estimator at $\theta$
-- statement:
--   For an estimator $\hat\theta$ (a map from the data $(X_i, Y_i)_{i\le n}$ and the auxiliary randomness $U$ to $\mathbb R^m$) and $\theta \in \mathbb R^m$, this is
--   $$
--   Q_{1-\delta,\theta}\bigl(\|\hat\theta - \theta\|_2^2\bigr),
--   $$
--   the $(1-\delta)$-quantile of the squared coefficient error when the data are drawn from model (1) with coefficient $\theta$. By orthonormality, $\|\hat\theta - \theta\|_2^2 = \mathbb E[(f_{\hat\theta} - f_\theta)^2]$ is the population prediction loss.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, p.3

import Mathlib
import Definitions.Def_CubeSampling_noiseSampleLaw
import Definitions.Def_CubeSampling_observe
import Definitions.Def_CubeSampling_quantile
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSampling

/-- The risk `Q_{1−δ,θ}(‖θ̂ − θ‖₂²)` of an estimator `θ̂` at the coefficient vector `θ` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1,
p.3): the `(1 − δ)`-quantile of the squared error under the data distribution of model (1) with
coefficient `θ`, the probability including the inputs, the noise and the estimator's randomness `U`.

**Formalization Note** An estimator is a map from the data `(X_i, Y_i)_{i ≤ n}` and `U ∈ [0, 1]`
to `ℝ^m`. -/
noncomputable def riskQuantile {d m : ℕ} (Φ : Fin m → Cube d → ℝ) (σ : ℝ) (n : ℕ) (δ : ℝ)
    (est : (Fin n → Cube d × ℝ) × unitInterval → (Fin m → ℝ)) (θ : Fin m → ℝ) : ℝ≥0∞ :=
  quantile (noiseSampleLaw d σ n)
    (fun ω => ENNReal.ofReal (∑ j, (est (observe Φ θ ω.1, ω.2) j - θ j) ^ 2)) δ

end CubeSampling


