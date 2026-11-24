-- Prove2me | Definitions.Def_HackingInterval_ATE_Supplement_GaussianEndpoints
-- name    : HackingInterval_ATE_Supplement_GaussianEndpoints
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:55:03.959452+00:00
-- url     : https://prove2.me/theorems/c90c841f-a143-4307-a9d7-e8337b3a7ed3
-- title:
--   Equation (19): fixed-design Gaussian outcomes and random hacking endpoints
-- statement:
--   Fix treatment covariates $X$, treatment assignments, the full matrix $\widetilde X$, a true coefficient vector $\beta\in\mathbb R^{p+1}$, and a noise standard deviation $\sigma\ge0$. The response law has independent coordinates
--
--   $$Y_i\sim N((\widetilde X\beta)_i,\sigma^2),\qquad\text{equivalently }Y\sim N(\widetilde X\beta,\sigma^2 I).$$
--
--   For each realized vector $Y$, substitute that vector into the published treatment-data object, recompute its least-squares residual $s(Y)=\mathrm{SSE}(Y)$, and set $\theta(Y)=(1+r)s(Y)$. The lower and upper random endpoints are
--
--   $$B_-(Y)=\beta^*_{0,\min}(Y,\theta(Y)),\qquad B_+(Y)=\beta^*_{0,\max}(Y,\theta(Y)).$$
--
--   This represents the random quantities whose conditional variances appear in Theorem 3. Fixing the design before integration is the meaning of conditioning on $\widetilde X$. No regression coefficient law, chi law, independence of fitted and residual components, or variance formula is built into the definition.
--
--   **Formalization Note** Mathlib's finite product of real Gaussian measures supplies the general probability object. At $\sigma=0$ the law is the point mass at the fitted true response. The data argument's original outcome vector is replaced, so it does not constrain the sampled $Y$.
-- source:
--   Coker, Rudin & King, A Theory of Statistical Inference for Ensuring the Robustness of Scientific Results, Management Science (Articles in Advance, 2021), DOI 10.1287/mnsc.2020.3818, p. 12 (PDF 13), §5.1.3, Equation (19) and Theorem 3

import Mathlib
import Definitions.Def_HackingInterval_ATE_Model
open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section

namespace HackingInterval.ATE.Supplement

/-- Fixed-design Equation (19), using independent Gaussian coordinates.
σ is the noise standard deviation, and σ = 0 is included. -/
def responseLaw {n p : ℕ} (D : TreatData n p)
    (β : Fin p ⊕ Unit → ℝ) (σ : ℝ≥0) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => gaussianReal ((D.Xt *ᵥ β) i) (σ ^ 2))

instance responseLaw_probability {n p : ℕ} (D : TreatData n p)
    (β : Fin p ⊕ Unit → ℝ) (σ : ℝ≥0) : IsProbabilityMeasure (responseLaw D β σ) := by
  unfold responseLaw
  infer_instance

/-- Reuse the published data object with a newly sampled outcome vector. -/
def withResponse {n p : ℕ} (D : TreatData n p) (Y : Fin n → ℝ) : TreatData n p :=
  { D with Y := Y }

/-- Lower bound as a random variable, with the same random Y in SSE and the threshold. -/
def lowerEndpoint {n p : ℕ} (D : TreatData n p) (r : ℝ) (Y : Fin n → ℝ) : ℝ :=
  let DY := withResponse D Y
  DY.beta0Min ((1 + r) * DY.SSE)

/-- Upper bound as a random variable, with the same random Y in SSE and the threshold. -/
def upperEndpoint {n p : ℕ} (D : TreatData n p) (r : ℝ) (Y : Fin n → ℝ) : ℝ :=
  let DY := withResponse D Y
  DY.beta0Max ((1 + r) * DY.SSE)

end HackingInterval.ATE.Supplement


