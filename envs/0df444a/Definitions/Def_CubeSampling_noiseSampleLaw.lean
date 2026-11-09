-- Prove2me | Definitions.Def_CubeSampling_noiseSampleLaw
-- name    : CubeSampling_noiseSampleLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:16:38.572775+00:00
-- url     : https://prove2.me/theorems/b2775718-68d1-478d-8249-353d170dcf69
-- title:
--   Law of inputs, noise and estimator randomness in model (1)
-- statement:
--   For $n$ samples and noise level $\sigma > 0$, this is the joint law of
--   $$
--   (X_i, \xi_i)_{i=1}^n \ \text{i.i.d.}, \quad X_i \sim \mu_d,\ \ \xi_i \sim N(0, \sigma^2) \ \text{independent},
--   $$
--   together with an independent $U \sim \mathrm{Uniform}[0,1]$ carrying the estimator's own randomness. Probabilities in the risk include the inputs, the noise and the estimator randomness.
--
--   **Formalization Note** A randomized estimator is a measurable function of the data and of $U$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, (1), p.3

import Mathlib
import Definitions.Def_CubeSampling_cubeMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSampling

/-- The law of the primitive randomness of model (1) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1, p.3): `n` i.i.d. pairs
`(X_i, ξ_i)` with `X_i ~ μ_d` and `ξ_i ~ N(0, σ²)` independent, together with an independent
`U ~ Uniform[0, 1]` that carries the estimator's own randomness ("probabilities include inputs,
noise, and any estimator randomness").

**Formalization Note** A randomized estimator is a measurable function of the data and of `U`. -/
noncomputable def noiseSampleLaw (d : ℕ) (σ : ℝ) (n : ℕ) :
    Measure ((Fin n → Cube d × ℝ) × unitInterval) :=
  (Measure.pi fun _ : Fin n => (cubeMeasure d).prod (gaussianReal 0 (σ ^ 2).toNNReal)).prod volume

end CubeSampling


