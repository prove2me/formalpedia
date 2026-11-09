-- Prove2me | Definitions.Def_IncoherentPurity_Adaptive_Gaussian
-- name    : IncoherentPurity_Adaptive_Gaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:12.238248+00:00
-- url     : https://prove2.me/theorems/b71110dc-fc0b-4ccb-aff0-4bb4ed81236d
-- title:
--   Gaussian encodings, adaptive noisy queries, and posterior statistics
-- statement:
--   For any Hilbert–Schmidt orthonormal real basis $V_r$ of traceless Hermitian matrices, set $D=d^2-1$, $\Delta_\theta=\sum_r\theta_rV_r$, and $\rho_\theta=I/d+\Delta_\theta$. These operators are defined for every real vector, including non-states. The operator norm uses the Euclidean operator norm. The two Gaussian priors have independent coordinates of variances $v_0=c_0\min(1,d\varepsilon)d^{-3}$ and $v_1=(1+\alpha)v_0$, where $\alpha=10\varepsilon/(Ddv_0)$. They are never conditioned on positivity. The purity concentration sets are computed from the trace polynomial and its Gaussian means.
--
--   A query policy has a parameter-independent classical seed and chooses a real vector from past responses; fresh response noise is standard Gaussian. A bound $L$ means every chosen vector has Euclidean norm at most $L$. Transcript densities integrate the product of the actual conditional Gaussian densities against the Gaussian prior. Posterior means and covariances are their Bayesian integrals. The score differentiates the log transcript density, and Fisher information is a nonnegative extended integral of its square. Total variation is the supremum over measurable events. Gaussian covariance updates retain singular positive semidefinite covariances.
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, definitions and constructions, PDF pp.18–23 = printed pp.18–23; Definition 6.5; equations (6.4)–(6.5), (6.23)–(6.24), (6.30)–(6.34); Definition 2.2

import Definitions.Def_IncoherentPurity_Adaptive_Measurements

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder
noncomputable section

namespace IncoherentPurity.Adaptive

abbrev Vec (D : ℕ) := Fin D → ℝ
def dot {D : ℕ} (a b : Vec D) : ℝ := ∑ i, a i * b i
def normSq {D : ℕ} (a : Vec D) := dot a a
def gaussianPrior (D : ℕ) (v : ℝ) : Measure (Vec D) :=
  Measure.pi (fun _ => gaussianReal 0 (Real.toNNReal v))

def gaussDim (d : ℕ) := d^2 - 1
structure Encoding (d : ℕ) where
  basis : Fin (gaussDim d) → Op d
  hermitian : ∀ i, (basis i).IsHermitian
  traceless : ∀ i, (basis i).trace = 0
  orthonormal : ∀ i j, ((basis i * basis j).trace).re = if i = j then 1 else 0
  spanning : ∀ A : Op d, A.IsHermitian → A.trace = 0 →
    ∃ θ : Vec (gaussDim d), A = ∑ i, θ i • basis i

def perturbation {d : ℕ} (E : Encoding d) (θ : Vec (gaussDim d)) : Op d :=
  ∑ i, θ i • E.basis i
def encoded {d : ℕ} (E : Encoding d) (θ : Vec (gaussDim d)) : Op d :=
  (1 / (d : ℝ)) • (1 : Op d) + perturbation E θ
/-- Operator norm on Euclidean space, not an entrywise matrix norm. -/
def opNorm {d : ℕ} (A : Op d) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖
def priorV0 (c₀ : ℝ) (d : ℕ) (ε : ℝ) := c₀ * min 1 ((d : ℝ)*ε) / (d : ℝ)^3
def priorAlpha (c₀ : ℝ) (d : ℕ) (ε : ℝ) :=
  10 * ε / ((gaussDim d : ℝ) * d * priorV0 c₀ d ε)
def priorV (c₀ : ℝ) (d : ℕ) (ε : ℝ) (i : Fin 2) :=
  if i = 0 then priorV0 c₀ d ε else (1 + priorAlpha c₀ d ε) * priorV0 c₀ d ε

def purityCenter (c₀ : ℝ) (d : ℕ) (ε : ℝ) (i : Fin 2) :=
  1 / (d : ℝ) + (gaussDim d : ℝ) * priorV c₀ d ε i
def goodPuritySet {d : ℕ} (E : Encoding d) (c₀ ε : ℝ) (i : Fin 2) : Set (Vec (gaussDim d)) :=
  {θ | |powerSum (encoded E θ) 2 - purityCenter c₀ d ε i| ≤ ε / (d : ℝ)}

/-- A parameter-independent classical policy. All randomness is in the seed; the only
access to the unknown vector is through the Gaussian query responses. -/
structure QueryPolicy (D : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  Seed : Type
  seedMS : MeasurableSpace Seed
  seedLaw : @Measure Seed seedMS
  seed_probability : @IsProbabilityMeasure Seed seedMS seedLaw
  query : ℕ → Seed × (ℕ → ℝ) → Vec D
  measurable_query : letI := seedMS; ∀ j i, Measurable (fun h => query j h i)
  output : Seed × (ℕ → ℝ) → Ω
  measurable_output : letI := seedMS; Measurable output
attribute [instance] QueryPolicy.seedMS

def IsBoundedQuery {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : QueryPolicy D Ω) (L : ℝ) : Prop :=
  0 ≤ L ∧ ∀ j h, normSq (P.query j h) ≤ L^2

def responsePrefix {n : ℕ} (y : Fin n → ℝ) (j : ℕ) : ℕ → ℝ :=
  fun i => if h : i < n then if i < j then y ⟨i,h⟩ else 0 else 0

def conditionalDensity {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : QueryPolicy D Ω) (n : ℕ) (θ : Vec D) (h : P.Seed × (Fin n → ℝ)) : ℝ :=
  ∏ j : Fin n, gaussianPDFReal (dot (P.query j (h.1, responsePrefix h.2 j)) θ) 1 (h.2 j)
def queryDensity {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : QueryPolicy D Ω) (n : ℕ) (v : ℝ) (h : P.Seed × (Fin n → ℝ)) : ℝ :=
  ∫ θ, conditionalDensity P n θ h ∂gaussianPrior D v

def queryLaw {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : QueryPolicy D Ω) (n : ℕ) (v : ℝ) : Measure (P.Seed × (Fin n → ℝ)) :=
  (P.seedLaw.prod volume).withDensity (fun h => ENNReal.ofReal (queryDensity P n v h))
def queryLawAt {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : QueryPolicy D Ω) (n : ℕ) (θ : Vec D) : Measure (P.Seed × (Fin n → ℝ)) :=
  (P.seedLaw.prod volume).withDensity (fun h => ENNReal.ofReal (conditionalDensity P n θ h))
def queryOutputLawAt {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : QueryPolicy D Ω) (n : ℕ) (θ : Vec D) : Measure Ω :=
  (queryLawAt P n θ).map (fun h => P.output (h.1,responsePrefix h.2 n))

def posteriorMean {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : QueryPolicy D Ω) (n : ℕ) (s : ℝ) (h : P.Seed × (Fin n → ℝ)) : Vec D :=
  fun i => (∫ θ, θ i * conditionalDensity P n θ h ∂gaussianPrior D (s^2)) /
    queryDensity P n (s^2) h

def posteriorCov {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : QueryPolicy D Ω) (n : ℕ) (s : ℝ) (h : P.Seed × (Fin n → ℝ)) : Matrix (Fin D) (Fin D) ℝ :=
  fun i j => (∫ θ, (θ i - posteriorMean P n s h i) * (θ j - posteriorMean P n s h j) *
    conditionalDensity P n θ h ∂gaussianPrior D (s^2)) / queryDensity P n (s^2) h

def queryScore {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : QueryPolicy D Ω) (n : ℕ) (s : ℝ) (h : P.Seed × (Fin n → ℝ)) : ℝ :=
  deriv (fun t => Real.log (queryDensity P n (t^2) h)) s
/-- Extended nonnegative Fisher information: nonintegrable scores have value infinity. -/
def queryFisher {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : QueryPolicy D Ω) (n : ℕ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ h, ENNReal.ofReal ((queryScore P n s h)^2) ∂queryLaw P n (s^2)

/-- TV on arbitrary measurable spaces as a supremum over measurable events. -/
def totalVariation {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) : ℝ≥0∞ :=
  ⨆ A : {A : Set Ω // MeasurableSet A}, max (μ A.val - ν A.val) (ν A.val - μ A.val)

/-- One Bayesian Gaussian update, including singular positive semidefinite covariance. -/
def updateB {D : ℕ} (C : Matrix (Fin D) (Fin D) ℝ) (a : Vec D) : Vec D :=
  (1 / Real.sqrt (1 + dot a (C *ᵥ a))) • (C *ᵥ a)
def innovation {D : ℕ} (m : Vec D) (C : Matrix (Fin D) (Fin D) ℝ) (a : Vec D) (y : ℝ) :=
  (y - dot a m) / Real.sqrt (1 + dot a (C *ᵥ a))
def updateMean {D : ℕ} (m : Vec D) (C : Matrix (Fin D) (Fin D) ℝ) (a : Vec D) (y : ℝ) :=
  m + innovation m C a y • updateB C a
def updateCov {D : ℕ} (C : Matrix (Fin D) (Fin D) ℝ) (a : Vec D) :=
  C - (Matrix.of fun i j => updateB C a i * updateB C a j)
def gaussianVector {D : ℕ} (m : Vec D) (C : Matrix (Fin D) (Fin D) ℝ) : Measure (Vec D) :=
  (multivariateGaussian (WithLp.toLp 2 m) C).map (fun x => fun i => x i)
def responseLaw {D : ℕ} (m : Vec D) (C : Matrix (Fin D) (Fin D) ℝ) (a : Vec D) : Measure ℝ :=
  gaussianReal (dot a m) (Real.toNNReal (1 + dot a (C *ᵥ a)))
def bayesPosterior {D : ℕ} (m : Vec D) (C : Matrix (Fin D) (Fin D) ℝ) (a : Vec D) (y : ℝ) :
    Measure (Vec D) :=
  (1 / ENNReal.ofReal (gaussianPDFReal (dot a m) (Real.toNNReal (1 + dot a (C *ᵥ a))) y)) •
    (gaussianVector m C).withDensity (fun θ => ENNReal.ofReal (gaussianPDFReal (dot a θ) 1 y))

end IncoherentPurity.Adaptive


