-- Prove2me | Definitions.Def_ParallelDiffusionLB_NearIsotropic_Gaussian
-- name    : ParallelDiffusionLB_NearIsotropic_Gaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:07.602367+00:00
-- url     : https://prove2.me/theorems/71f78bbb-c7e7-4bcb-97d2-16a8154b4d12
-- title:
--   Gaussian smoothing, pointwise scores, legal oracles and moments
-- statement:
--   Let $E_d=\mathbb R^d$ with its Euclidean norm and Borel sigma algebra. For a probability measure $\mu$ and $\tau>0$, Gaussian smoothing is the law of $Y+\tau Z$, where $Y\sim\mu$ and $Z\sim N(0,I_d)$ are independent. Its specified everywhere-positive density and score are
--   $$p_{\mu,\tau}(x)=\int (\sqrt{2\pi}\tau)^{-d}e^{-\|x-y\|^2/(2\tau^2)}\,d\mu(y),\qquad s_{\mu,\tau}=\nabla\log p_{\mu,\tau}.$$
--   The Gaussian posterior is the prior weighted by this likelihood and normalized by $p_{\mu,\tau}(x)$, at every $x$. Its mean and covariance provide the pointwise conditional moments. For finite nonempty $C$, the target is the equal-weight mixture $|C|^{-1}\sum_{y\in C}N(y,\gamma^2I_d)$.
--
--   A legal oracle is a fixed jointly measurable map $\hat s(x,\sigma)$ with $\sigma>0$ and, for every such $\sigma$,
--   $$\int\|\hat s(x,\sigma)-s_{\mu,\sigma}(x)\|^2\,d\mu^{(\sigma)}(x)\le\varepsilon^2/\sigma^2.$$
--   This nonnegative integral takes extended values. Mean and covariance use their usual integrals, used here only for laws with finite second moments. Near-isotropy at tolerance $t$ means $\|E_\mu X\|\le t$ and $\|\operatorname{Cov}(\mu)-(1+\gamma^2)I_d\|_{op}\le t$.
--
--   These definitions keep the score defined at all query points and fix the common probabilistic interface.
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, §2.1–2.3, pp. 5–6; Instance geometry and (17), pp. 19–20

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

/-- Euclidean space, with its Borel sigma algebra. Source: §2, p. 5. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The centered Gaussian with covariance `τ² I`, including the Dirac law at `τ=0`. -/
def gaussianLaw (d : ℕ) (τ : ℝ) : Measure (E d) :=
  (stdGaussian (E d)).map (fun z => τ • z)

/-- The positive Gaussian density, used only at `τ>0`. -/
def gaussianDensity (d : ℕ) (τ : ℝ) (x : E d) : ℝ :=
  (Real.sqrt (2 * Real.pi) * τ) ^ (-(d : ℤ)) * Real.exp (-‖x‖ ^ 2 / (2 * τ ^ 2))

/-- Law of `Y+τZ` for independent `Y~μ` and standard Gaussian `Z`. -/
def smoothLaw {d : ℕ} (μ : Measure (E d)) (τ : ℝ) : Measure (E d) :=
  (μ.prod (stdGaussian (E d))).map (fun p => p.1 + τ • p.2)

/-- Everywhere defined convolution density, rather than an a.e. RN representative. -/
def smoothDensity {d : ℕ} (μ : Measure (E d)) (τ : ℝ) (x : E d) : ℝ :=
  ∫ y, gaussianDensity d τ (x - y) ∂μ

/-- Score of the explicit Gaussian smoothing density; §2.1. -/
def score {d : ℕ} (μ : Measure (E d)) (τ : ℝ) : E d → E d :=
  gradient (fun x => Real.log (smoothDensity μ τ x))

/-- Finite-set uniform law. The empty set gives the zero measure, never used as a target. -/
def uniformFinset {α : Type*} [MeasurableSpace α] (S : Finset α) : Measure α :=
  (S.card : ℝ≥0∞)⁻¹ • ∑ y ∈ S, Measure.dirac y

/-- Equal-weight Gaussian mixture with the specified distinct centers. -/
def mixture {d : ℕ} (C : Finset (E d)) (γ : ℝ) : Measure (E d) :=
  smoothLaw (uniformFinset C) γ

/-- Extended nonnegative squared error, so nonintegrability never yields zero. -/
def squaredError {d : ℕ} (μ : Measure (E d)) (f g : E d → E d) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖f x - g x‖ ^ 2) ∂μ

/-- A query contains a strictly positive additional noise level. -/
abbrev Query (d : ℕ) := E d × {σ : ℝ // 0 < σ}

/-- Fixed, jointly measurable score oracle with the distributional guarantee (1). -/
def LegalOracle {d : ℕ} (μ : Measure (E d)) (ε : ℝ) (o : Query d → E d) : Prop :=
  Measurable o ∧ ∀ σ : {σ : ℝ // 0 < σ},
    squaredError (smoothLaw μ σ.1) (fun x => o (x, σ)) (score μ σ.1) ≤
      ENNReal.ofReal (ε ^ 2 / σ.1 ^ 2)

/-- Mean and covariance operator for laws with finite second moments. -/
def mean {d : ℕ} (μ : Measure (E d)) : E d := ∫ x, x ∂μ

def covarianceOp {d : ℕ} (μ : Measure (E d)) : E d →L[ℝ] E d :=
  ∫ x, (innerSL ℝ (x - mean μ)).smulRight (x - mean μ) ∂μ

/-- Explicit near-isotropy event (17), at a variable tolerance. -/
def IsNearIsotropic {d : ℕ} (μ : Measure (E d)) (γ t : ℝ) : Prop :=
  ‖mean μ‖ ≤ t ∧
  ‖covarianceOp μ - (1 + γ ^ 2) • ContinuousLinearMap.id ℝ (E d)‖ ≤ t

/-- Gaussian posterior specified at every point by weighting the prior likelihood. -/
def posterior {d : ℕ} (μ : Measure (E d)) (τ : ℝ) (x : E d) : Measure (E d) :=
  μ.withDensity (fun y => ENNReal.ofReal (gaussianDensity d τ (x-y) / smoothDensity μ τ x))

/-- Pointwise conditional moments in (19)–(20). -/
def posteriorMean {d : ℕ} (μ : Measure (E d)) (τ : ℝ) (x : E d) : E d :=
  mean (posterior μ τ x)

def posteriorCov {d : ℕ} (μ : Measure (E d)) (τ : ℝ) (x : E d) : E d →L[ℝ] E d :=
  covarianceOp (posterior μ τ x)

end ParallelDiffusionLB.NearIsotropic


