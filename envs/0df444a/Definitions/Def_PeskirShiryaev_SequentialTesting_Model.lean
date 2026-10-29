-- Prove2me | Definitions.Def_PeskirShiryaev_SequentialTesting_Model
-- name    : PeskirShiryaev_SequentialTesting_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:25:25.571332+00:00
-- url     : https://prove2.me/theorems/a66daad9-1a62-468c-aa8b-194e7e027cec
-- title:
--   Wiener testing experiment and continuous posterior
-- statement:
--   Let $\mu\ne0$, $\sigma\ne0$, $a,b>0$ and $T>0$. The observation is $X_u=\theta\mu u+\sigma W_u$, where $\theta\in\{0,1\}$ is unobserved. Under the two component probability laws $P_0,P_1$, the hypothesis is respectively zero or one and $W$ is standard Brownian motion. For prior $p\in[0,1]$ the experiment uses $P_p=pP_1+(1-p)P_0$. The common Brownian path law makes $W$ independent of $\theta$ under this mixture.
--
--   Write $\mathcal F^X_u=\sigma(X_s:0\le s\le u)$. Define
--   $$L_u=\exp\!\left\{\frac{\mu}{\sigma^2}\left(X_u-\frac\mu2u\right)\right\},\qquad \Pi^p_u=\frac{pL_u}{1-p+pL_u},\qquad c=\frac b{a+b},\qquad H(p)=\min\{ap,b(1-p)\}.$$
--   The posterior interpretation of $\Pi$ is a theorem; it is not assumed in the experiment. These definitions supply the observation model and the two terminal losses for all subsequent results.
--
--   **Formalization Note** Time is nonnegative real time. Brownian paths are represented by continuous, zero-started versions everywhere, and each coordinate is measurable. The rational posterior formula includes $p=0,1$ by continuous extension of the book's odds expression. Neither $\mu$ nor $\sigma$ is sign-normalized.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 287–289 / PDF pp. 304–306, Eqs. (21.0.1)–(21.0.10)

import Mathlib
import Mathlib.Probability.BrownianMotion.Basic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PeskirShiryaev.SequentialTesting

/-- The parameters of the two-hypothesis, finite-horizon experiment. No sign
normalization of the drift or noise coefficient is imposed. -/
structure Parameters where
  μ : ℝ
  σ : ℝ
  a : ℝ
  b : ℝ
  T : ℝ
  drift_ne : μ ≠ 0
  noise_ne : σ ≠ 0
  a_pos : 0 < a
  b_pos : 0 < b
  horizon_pos : 0 < T

/-- The two component laws of (21.0.1). Under each component the driving
process is standard Brownian motion and the hypothesis is fixed. Thus under
their mixture the hypothesis is independent of the whole Brownian path.
Continuous, zero-started versions are selected on every sample path. -/
structure Model (Ω : Type*) [MeasurableSpace Ω] where
  P0 : Measure Ω
  P1 : Measure Ω
  prob0 : IsProbabilityMeasure P0
  prob1 : IsProbabilityMeasure P1
  θ : Ω → Bool
  θ_measurable : Measurable θ
  θ_zero : ∀ᵐ ω ∂P0, θ ω = false
  θ_one : ∀ᵐ ω ∂P1, θ ω = true
  W : ℝ≥0 → Ω → ℝ
  W_measurable : ∀ u, Measurable (W u)
  W_continuous : ∀ ω, Continuous (fun u => W u ω)
  W_zero : ∀ ω, W 0 ω = 0
  brownian0 : IsBrownianReal W P0
  brownian1 : IsBrownianReal W P1

noncomputable def prior {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (p : ℝ) : Measure Ω :=
  ENNReal.ofReal p • E.P1 + ENNReal.ofReal (1 - p) • E.P0

noncomputable def observation {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (C : Parameters) (u : ℝ≥0) (ω : Ω) : ℝ :=
  (if E.θ ω then C.μ * (u : ℝ) else 0) + C.σ * E.W u ω

/-- Exactly the observation sigma field; it does not reveal θ or W. -/
@[instance_reducible]
noncomputable def observationSigma {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (C : Parameters) (u : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ s ≤ u, MeasurableSpace.comap (observation E C s) inferInstance

/-- The exponential expression in (21.0.7). Its likelihood-ratio and posterior
interpretation is a theorem, not a field of Model. -/
noncomputable def likelihood {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (C : Parameters) (u : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (C.μ / C.σ ^ 2 * (observation E C u ω - C.μ / 2 * (u : ℝ)))

/-- The continuous posterior version. Algebraically (21.0.8), extended to
priors 0 and 1 by their deterministic values. -/
noncomputable def posterior {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (C : Parameters) (p : ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  p * likelihood E C u ω / (1 - p + p * likelihood E C u ω)

noncomputable def cutoff (C : Parameters) : ℝ := C.b / (C.a + C.b)

noncomputable def terminalLoss (C : Parameters) (p : ℝ) : ℝ :=
  min (C.a * p) (C.b * (1 - p))

end PeskirShiryaev.SequentialTesting


