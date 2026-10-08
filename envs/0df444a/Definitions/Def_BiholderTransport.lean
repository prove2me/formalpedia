-- Prove2me | Definitions.Def_BiholderTransport
-- name    : BiholderTransport
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:01.638276+00:00
-- url     : https://prove2.me/theorems/5d4b3a22-2c9d-4ce8-bece-82aa6ece24aa
-- statement:
--   For an n-dimensional real Euclidean model, the transport cost on a metric space is c(x,y)=d(x,y)²/2. Metric volume is n-dimensional Hausdorff measure multiplied by the ratio of Euclidean volume to Hausdorff measure of the Euclidean unit ball. A density ρ is admissible relative to a measure vol and real bounds λ and Λ when it is almost everywhere measurable, integrable, has integral one, and satisfies λ≤ρ≤Λ almost everywhere; positivity of the bounds is not separately required. Its associated measure has density max(ρ,0) with respect to vol. A map T is optimal when it is measurable, pushes the measure associated with ρ₀ to that associated with ρ₁, and minimizes ∫c(x,T(x))ρ₀(x) dvol among all measurable maps with that pushforward. A homeomorphism satisfies the bi-Hölder estimate with parameters α,C when both it and its inverse satisfy d(f(x),f(y))≤C d(x,y)^α globally, using the same parameters. On a smooth manifold with a metric and Riemannian tangent bundle, a geodesic with initial data (x,v) is a smooth curve γ:ℝ→M whose position and derivative at zero are x and v and which, near each time, satisfies d(γ(s),γ(u))=|s−u|‖v‖. The exponential expₓ(v) is the time-one value of a chosen such curve when one exists, and is x otherwise; uniqueness is not part of this definition. The injectivity domain at x consists of vectors p for which some a>1 satisfies d(x,expₓ(ap))=a‖p‖. Define MTW(x,p;ξ,η) as −3/2 times the second derivative in s, at zero, of the second derivative in t, at zero, of c(expₓ(tξ),expₓ(p+sη)). WeakMTW is the proposition that this quantity is nonnegative at every x and every p in its injectivity domain whenever ξ and η are orthogonal tangent vectors at x.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BiholderTransport.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BiholderTransport.lean; bytes 16..4068
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport

abbrev Model (n : ℕ) := EuclideanSpace ℝ (Fin n)

section MetricDefinitions

variable {M : Type*} [MetricSpace M]

/-- Squared-distance cost with factor one half. -/
def cost (x y : M) : ℝ := dist x y ^ 2 / 2

/-- Calibration of Hausdorff measure to Euclidean volume. -/
def euclideanVolumeFactor (n : ℕ) : ℝ≥0∞ :=
  volume (Metric.ball (0 : Model n) 1) /
    (Measure.hausdorffMeasure (n : ℝ) : Measure (Model n))
      (Metric.ball (0 : Model n) 1)

variable [MeasurableSpace M]

/-- Riemannian volume calibrated to Lebesgue measure in Euclidean space. -/
def metricVolume [BorelSpace M] (n : ℕ) : Measure M :=
  euclideanVolumeFactor n • Measure.hausdorffMeasure (n : ℝ)

/-- Almost-everywhere measurable probability densities between fixed bounds. -/
def AdmissibleDensity (vol : Measure M) (lam cap : ℝ) (rho : M → ℝ) : Prop :=
  AEMeasurable rho vol ∧ Integrable rho vol ∧
  (∫ x, rho x ∂vol) = 1 ∧ (∀ᵐ x ∂vol, lam ≤ rho x ∧ rho x ≤ cap)

/-- Multiplication by a density, ignoring exceptional negative values on null sets. -/
def densityMeasure (vol : Measure M) (rho : M → ℝ) : Measure M :=
  vol.withDensity (fun x => ENNReal.ofReal (rho x))

/-- Optimality for the Monge minimization problem. -/
def IsOptimalMap (vol : Measure M) (rho0 rho1 : M → ℝ) (T : M → M) : Prop :=
  Measurable T ∧ Measure.map T (densityMeasure vol rho0) = densityMeasure vol rho1 ∧
  ∀ S : M → M, Measurable S →
    Measure.map S (densityMeasure vol rho0) = densityMeasure vol rho1 →
    (∫ x, cost x (T x) * rho0 x ∂vol) ≤
      (∫ x, cost x (S x) * rho0 x ∂vol)

/-- The two global estimates have the very same exponent and constant. -/
def BiHolderEstimate (alpha C : ℝ) (T : M ≃ₜ M) : Prop :=
  (∀ x x', dist (T x) (T x') ≤ C * (dist x x') ^ alpha) ∧
  (∀ y y', dist (T.symm y) (T.symm y') ≤ C * (dist y y') ^ alpha)

end MetricDefinitions

section RiemannianDefinitions

variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold 𝓘(ℝ, Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]

/-- Complete affinely parametrized geodesic with prescribed initial tangent.
Local metric minimization is an intrinsic definition of Riemannian geodesics. -/
def IsGeodesicWithInitialData (x : M) (v : TangentSpace 𝓘(ℝ, Model n) x)
    (gamma : ℝ → M) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n) ∞ gamma ∧
  (⟨gamma 0, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n) gamma 0 (1 : ℝ)⟩ :
    TangentBundle 𝓘(ℝ, Model n) M) = ⟨x, v⟩ ∧
  ∀ t : ℝ, ∃ eps : ℝ, 0 < eps ∧
    ∀ s u : ℝ, |s - t| < eps → |u - t| < eps →
      dist (gamma s) (gamma u) = |s - u| * ‖v‖

/-- Evaluation at time one of the geodesic determined by initial data. -/
def riemannianExp (x : M) (v : TangentSpace 𝓘(ℝ, Model n) x) : M := by
  classical
  exact if h : ∃ gamma, IsGeodesicWithInitialData x v gamma then (Classical.choose h) 1 else x

/-- The open injectivity domain, defined by extendible minimizing vectors. -/
def injectivityDomain (x : M) : Set (TangentSpace 𝓘(ℝ, Model n) x) :=
  {p | ∃ a : ℝ, 1 < a ∧ dist x (riemannianExp x (a • p)) = a * ‖p‖}

/-- The Ma–Trudinger–Wang fourth derivative with factor -3/2. -/
def mtw (x : M) (p xi eta : TangentSpace 𝓘(ℝ, Model n) x) : ℝ :=
  -(3 / 2 : ℝ) *
    iteratedDeriv 2 (fun s : ℝ =>
      iteratedDeriv 2 (fun t : ℝ =>
        cost (riemannianExp x (t • xi)) (riemannianExp x (p + s • eta))) 0) 0

/-- Weak MTW only at interior velocities and only for orthogonal test vectors. -/
def WeakMTW : Prop :=
  ∀ (x : M) (p : TangentSpace 𝓘(ℝ, Model n) x), p ∈ injectivityDomain x →
    ∀ xi eta : TangentSpace 𝓘(ℝ, Model n) x,
      inner ℝ xi eta = 0 → 0 ≤ mtw x p xi eta

end RiemannianDefinitions



end WeakMTWTransport
end
end OAI


