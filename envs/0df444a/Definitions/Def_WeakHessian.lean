-- Prove2me | Definitions.Def_WeakHessian
-- name    : WeakHessian
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:38.378687+00:00
-- url     : https://prove2.me/theorems/2b8de190-6efa-4b06-ac2e-5844e7c23dd5
-- statement:
--   On a metric space X (and, where indicated, with a Borel measure m), this block builds the metric-measure machinery behind a weak Hessian upper bound. Time is [0,1], a curve is a continuous map from [0,1] to X, and a geodesic has dist(γs,γt)=|s−t|·dist(γ0,γ1). The metric speed is a limsup of difference quotients, and IsAC2 asks for a measurable control a with finite integral of a² and edist(γs,γt) ≤ ∫ from s to t of a. A test plan is a probability measure on curves with bounded compression (each time marginal is at most C·m), almost-sure AC² curves, and finite average kinetic energy. Local weak upper gradients D of f are locally L², a.e. nonnegative, and satisfy ∫|f(γ1)−f(γ0)| ≤ ∫∫ D(γt)·speed over all test plans with uniformly bounded tracks; the minimal one is the a.e. smallest, weakGradient picks a representative (zero if none exists), and Sobolev requires f and its weak gradient in L². The polarized form gamma(f,g)=(|∇(f+g)|²−|∇(f−g)|²)/4 defines the Laplacian weakly via ∫gamma(u,v)=−∫Lv for Sobolev v. Test functions are bounded, globally Lipschitz, in the Laplacian domain, with Sobolev Laplacian. weakHessian(F,g,h) is −∫(gamma(h,g)+h·Δg)·gamma(F,g) − ∫h·gamma(F,gamma(g,g)/2), and WeakHessianUpperBound(F,G) says it is at most ∫h·G·gamma(g,g) for all compactly supported test functions g and nonnegative compactly supported Lipschitz h. The block also defines local slope, Cheeger energy as an L² relaxation of half the squared slope, its quadratic (parallelogram) property, LSV distortion coefficients sigmaCoeff and tauCoeff, second moments, couplings, quadratic transport cost, optimal couplings, and the unreduced CurvatureDimension condition CD(K,N) via geodesic optimal plans and Rényi entropy integrals. RCD(K,N) combines CD(K,N) with quadratic Cheeger energy; FullSupport and FiniteOnBoundedSets are measure conditions; and CurveSecondDerivativeBound(F,G,σ) states that, for nonnegative smooth test functions φ supported in (0,1), ∫F(σt)φ'' ≤ dist(σ0,σ1)²·∫G(σt)φ.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/WeakHessian.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/WeakHessian.lean; bytes 16..9663
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian

abbrev Time := Set.Icc (0 : ℝ) 1

def timeZero : Time := ⟨0, le_rfl, zero_le_one⟩
def timeOne : Time := ⟨1, zero_le_one, le_rfl⟩

def clampTime (t : ℝ) : Time :=
  ⟨max 0 (min 1 t), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

variable {X : Type*} [MetricSpace X]

abbrev Curve (X : Type*) [MetricSpace X] := C(Time, X)

instance curveMeasurableSpace : MeasurableSpace (Curve X) := borel (Curve X)

instance curveBorelSpace : BorelSpace (Curve X) := ⟨rfl⟩

def evalReal (γ : Curve X) (t : ℝ) : X := γ (clampTime t)

/-- The constant-speed minimizing parametrization, including constant curves. -/
def IsGeodesic (γ : Curve X) : Prop :=
  ∀ s t : Time,
    dist (γ s) (γ t) = |(s : ℝ) - (t : ℝ)| * dist (γ timeZero) (γ timeOne)

/-- Metric speed. Limsup agrees a.e. with the metric derivative on AC² curves. -/
def metricSpeed (γ : Curve X) (t : ℝ) : ℝ≥0∞ :=
  Filter.limsup (fun s : ℝ => ENNReal.ofReal
    (dist (evalReal γ s) (evalReal γ t) / |s - t|)) (𝓝[≠] t)

/-- Absolute continuity with a square-integrable metric control. -/
def IsAC2 (γ : Curve X) : Prop :=
  ∃ a : ℝ → ℝ≥0∞, Measurable a ∧
    (∫⁻ t in Set.Icc (0 : ℝ) 1, (a t) ^ 2) < ∞ ∧
    ∀ s t : Time, (s : ℝ) ≤ (t : ℝ) →
      edist (γ s) (γ t) ≤ ∫⁻ r in Set.Icc (s : ℝ) (t : ℝ), a r

variable [MeasurableSpace X] [BorelSpace X]

/-- A 2-test plan: bounded compression and finite average kinetic energy. -/
def IsTestPlan (m : Measure X) (π : Measure (Curve X)) : Prop :=
  IsProbabilityMeasure π ∧
  (∃ C : ℝ≥0, ∀ t : Time,
    Measure.map (fun γ : Curve X => γ t) π ≤ (C : ℝ≥0∞) • m) ∧
  (∀ᵐ γ ∂π, IsAC2 γ) ∧
  (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1, (metricSpeed γ t) ^ 2 ∂volume ∂π) < ∞

/-- Uniform bounded spatial support; used only to define the local Sobolev class. -/
def BoundedTracks (π : Measure (Curve X)) : Prop :=
  ∃ o : X, ∃ R : ℝ, 0 < R ∧ ∀ᵐ γ ∂π, ∀ t : Time, dist (γ t) o ≤ R

def LocallyL2 (m : Measure X) (f : X → ℝ) : Prop :=
  ∀ o : X, ∀ R : ℝ, 0 < R → MemLp f 2 (m.restrict (Metric.ball o R))

/-- Local weak upper gradients, in the integrated test-plan definition. -/
def IsLocalWeakUpperGradient (m : Measure X) (f D : X → ℝ) : Prop :=
  LocallyL2 m D ∧ (∀ᵐ x ∂m, 0 ≤ D x) ∧
  ∀ π : Measure (Curve X), IsTestPlan m π → BoundedTracks π →
    (∫⁻ γ, ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ∂π) ≤
      ∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t ∂volume ∂π

def IsMinimalLocalWeakUpperGradient (m : Measure X) (f D : X → ℝ) : Prop :=
  IsLocalWeakUpperGradient m f D ∧
  ∀ D' : X → ℝ, IsLocalWeakUpperGradient m f D' → ∀ᵐ x ∂m, D x ≤ D' x

/-- A representative of the minimal weak upper gradient (zero off its domain). -/
def weakGradient (m : Measure X) (f : X → ℝ) : X → ℝ :=
  if h : ∃ D, IsMinimalLocalWeakUpperGradient m f D then Classical.choose h
  else 0

def LocalSobolev (m : Measure X) (f : X → ℝ) : Prop :=
  LocallyL2 m f ∧ ∃ D, IsMinimalLocalWeakUpperGradient m f D

def Sobolev (m : Measure X) (f : X → ℝ) : Prop :=
  MemLp f 2 m ∧ LocalSobolev m f ∧ MemLp (weakGradient m f) 2 m

/-- Polarization of the minimal weak gradient on an infinitesimally Hilbertian space. -/
def gamma (m : Measure X) (f g : X → ℝ) (x : X) : ℝ :=
  ((weakGradient m (fun y => f y + g y) x) ^ 2 -
    (weakGradient m (fun y => f y - g y) x) ^ 2) / 4

/-- Weak nonpositive generator convention, without a global L² assumption on F. -/
def IsLaplacian (m : Measure X) (u L : X → ℝ) : Prop :=
  Sobolev m u ∧ MemLp L 2 m ∧
    ∀ v : X → ℝ, Sobolev m v →
      (∫ x, gamma m u v x ∂m) = -(∫ x, L x * v x ∂m)

def InLaplacianDomain (m : Measure X) (u : X → ℝ) : Prop :=
  ∃ L, IsLaplacian m u L

def laplacian (m : Measure X) (u : X → ℝ) : X → ℝ :=
  if h : ∃ L, IsLaplacian m u L then Classical.choose h else 0

def BoundedFunction (f : X → ℝ) : Prop := ∃ B : ℝ, ∀ x, |f x| ≤ B

def GloballyLipschitz (f : X → ℝ) : Prop := ∃ L : ℝ≥0, LipschitzWith L f

/-- Bounded globally Lipschitz Laplacian-domain functions with Sobolev Laplacian. -/
def IsTestFunction (m : Measure X) (g : X → ℝ) : Prop :=
  InLaplacianDomain m g ∧ BoundedFunction g ∧ GloballyLipschitz g ∧
    Sobolev m (laplacian m g)

/-- The weak Hessian, with ∇_(∇g)∇g = ∇(Γ(g)/2). -/
def weakHessian (m : Measure X) (F g h : X → ℝ) : ℝ :=
  -(∫ x, (gamma m h g x + h x * laplacian m g x) * gamma m F g x ∂m) -
    ∫ x, h x * gamma m F (fun y => gamma m g g y / 2) x ∂m

def WeakHessianUpperBound (m : Measure X) (F G : X → ℝ) : Prop :=
  ∀ g : X → ℝ, IsTestFunction m g → HasCompactSupport g →
    ∀ h : X → ℝ, GloballyLipschitz h → HasCompactSupport h →
      (∀ x, 0 ≤ h x) →
      weakHessian m F g h ≤ ∫ x, h x * G x * gamma m g g x ∂m

/-- Asymptotic Lipschitz slope; zero at an isolated point. -/
def localSlope (f : X → ℝ) (x : X) : ℝ≥0∞ :=
  Filter.limsup (fun y => ENNReal.ofReal (|f y - f x| / dist y x)) (𝓝[≠] x)

/-- Cheeger energy is the L² relaxation of one half the squared local slope. -/
def cheegerEnergy (m : Measure X) (f : X → ℝ) : ℝ≥0∞ :=
  if MemLp f 2 m then
    sInf {a | ∃ fs : ℕ → X → ℝ,
      (∀ n, GloballyLipschitz (fs n) ∧ MemLp (fs n) 2 m) ∧
      Tendsto (fun n => eLpNorm (fun x => fs n x - f x) 2 m) atTop (𝓝 0) ∧
      a = Filter.liminf (fun n => (2 : ℝ≥0∞)⁻¹ *
        ∫⁻ x, (localSlope (fs n) x) ^ 2 ∂m) atTop}
  else ∞

def QuadraticCheegerEnergy (m : Measure X) : Prop :=
  ∀ f g : X → ℝ, cheegerEnergy m f < ∞ → cheegerEnergy m g < ∞ →
    cheegerEnergy m (fun x => f x + g x) + cheegerEnergy m (fun x => f x - g x) =
      2 * cheegerEnergy m f + 2 * cheegerEnergy m g

/-- The unreduced Lott–Sturm–Villani distortion coefficient σ. -/
def sigmaCoeff (K N t θ : ℝ) : ℝ≥0∞ :=
  if t ≤ 0 then 0 else if 1 ≤ t then 1 else
  if θ = 0 then ENNReal.ofReal t else
  if 0 < K then
    if K * θ ^ 2 < N * Real.pi ^ 2 then
      ENNReal.ofReal (Real.sin (t * θ * Real.sqrt (K / N)) /
        Real.sin (θ * Real.sqrt (K / N)))
    else ∞
  else if K = 0 then ENNReal.ofReal t else
    ENNReal.ofReal (Real.sinh (t * θ * Real.sqrt (-K / N)) /
      Real.sinh (θ * Real.sqrt (-K / N)))

/-- The τ coefficient (not the reduced σ coefficient) in CD(K,N). -/
def tauCoeff (K N t θ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal t) ^ (1 / N) * (sigmaCoeff K (N - 1) t θ) ^ ((N - 1) / N)

def HasSecondMoment (μ : Measure X) : Prop :=
  ∃ o : X, (∫⁻ x, (edist x o) ^ 2 ∂μ) < ∞

def IsCoupling (q : Measure (X × X)) (μ₀ μ₁ : Measure X) : Prop :=
  Measure.map Prod.fst q = μ₀ ∧ Measure.map Prod.snd q = μ₁

def QuadraticTransportCost (q : Measure (X × X)) : ℝ≥0∞ :=
  ∫⁻ p, (edist p.1 p.2) ^ 2 ∂q

def IsOptimalCoupling (q : Measure (X × X)) (μ₀ μ₁ : Measure X) : Prop :=
  IsCoupling q μ₀ μ₁ ∧ ∀ q' : Measure (X × X), IsCoupling q' μ₀ μ₁ →
    QuadraticTransportCost q ≤ QuadraticTransportCost q'

def endpointCoupling (π : Measure (Curve X)) : Measure (X × X) :=
  Measure.map (fun γ : Curve X => (γ timeZero, γ timeOne)) π

def interpolation (π : Measure (Curve X)) (t : Time) : Measure X :=
  Measure.map (fun γ : Curve X => γ t) π

/-- The positive of minus the N-Rényi entropy; singular mass contributes zero. -/
def renyiIntegral (m μ : Measure X) (N : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (μ.rnDeriv m x) ^ (1 - 1 / N) ∂m

/-- Unreduced CD(K,N), written with the standard dynamical optimal-plan formula. -/
def CurvatureDimension (m : Measure X) (K N : ℝ) : Prop :=
  ∀ μ₀ μ₁ : Measure X,
    IsProbabilityMeasure μ₀ → IsProbabilityMeasure μ₁ →
    HasSecondMoment μ₀ → HasSecondMoment μ₁ →
    μ₀ ≪ m → μ₁ ≪ m →
    ∃ π : Measure (Curve X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling π) μ₀ μ₁ ∧
      ∀ N' : ℝ, N ≤ N' → ∀ t : Time,
        (∫⁻ γ,
          (tauCoeff K N' (1 - (t : ℝ)) (dist (γ timeZero) (γ timeOne)) *
            (μ₀.rnDeriv m (γ timeZero)) ^ (-1 / N') +
          tauCoeff K N' (t : ℝ) (dist (γ timeZero) (γ timeOne)) *
            (μ₁.rnDeriv m (γ timeOne)) ^ (-1 / N')) ∂π) ≤
        renyiIntegral m (interpolation π t) N'

def RCD (m : Measure X) (K N : ℝ) : Prop :=
  CurvatureDimension m K N ∧ QuadraticCheegerEnergy m

def FullSupport (m : Measure X) : Prop :=
  ∀ U : Set X, IsOpen U → U.Nonempty → 0 < m U

def FiniteOnBoundedSets (m : Measure X) : Prop :=
  ∀ B : Set X, Bornology.IsBounded B → m B < ∞

/-- The literal second-distributional-derivative conclusion on (0,1). -/
def CurveSecondDerivativeBound (F G : X → ℝ) (σ : Curve X) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ Set.Ioo (0 : ℝ) 1 → (∀ t, 0 ≤ φ t) →
    (∫ t in Set.Icc (0 : ℝ) 1,
      F (evalReal σ t) * deriv (deriv φ) t) ≤
    (dist (σ timeZero) (σ timeOne)) ^ 2 *
      ∫ t in Set.Icc (0 : ℝ) 1, G (evalReal σ t) * φ t



end WeakHessian
end
end OAI


