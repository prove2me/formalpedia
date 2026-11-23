-- Prove2me | Definitions.Def_NoHair_staticReflectionAndCap
-- name    : NoHair_staticReflectionAndCap
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T10:47:32.599693+00:00
-- url     : https://prove2.me/theorems/3f6eac0b-fffd-4154-ba94-3a2e3e67beec
-- title:
--   Finite static reflection and a smooth point chart at the minus infinity
-- statement:
--   Separate the manifold reflected at the finite horizon from a local smooth positive metric filling the negative end. Include length control in the ordinary inversion chart.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticConformalCompletion
import Mathlib.Geometry.Euclidean.Inversion.Calculus

noncomputable section
open Set Filter Bundle
open scoped Bundle Topology Manifold ContDiff
namespace NoHair

/-- Coordinate quadratic form used to measure lengths on either copy. -/
def staticChartQuadratic (g : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (x v : ADMPoint) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, g x i j * v i * v j

/-- Upper metric bounds on the negative end and in the ordinary unit-inversion chart. -/
def HasStaticMinusInversionBound (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  let g := staticPositiveMetric (fun y => -N y) h
  let inv := EuclideanGeometry.inversion (0 : ADMPoint) 1
  ∃ R C : ℝ, 0 < R ∧ 0 < C ∧
    (∀ x : ADMPoint, R < ‖x‖ → ∀ v, ‖x‖^4 * staticChartQuadratic g x v ≤ C * ‖v‖^2) ∧
    ∀ y : ADMPoint, 0 < ‖y‖ → ‖y‖ < 1/R → ∀ v,
      staticChartQuadratic g (inv y) (fderiv ℝ inv y v) ≤ C * ‖v‖^2

/-- A local smooth, positive one-point filling of the negative spatial end.
Its coordinates may change the asymptotically flat gauge before inversion. -/
structure StaticMinusPointChart (Ω : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) where
  radius : ℝ
  positive : 0 < radius
  change : OpenPartialHomeomorph ADMPoint ADMPoint
  source : change.source = Metric.ball 0 radius ∩ ({0} : Set ADMPoint)ᶜ
  inside : change.target ⊆ Ω
  smoothChange : ContDiffOn ℝ ∞ change change.source
  smoothInverse : ContDiffOn ℝ ∞ change.symm change.target
  tendsOut : Tendsto (fun y => ‖change y‖) (𝓝[≠] (0:ADMPoint)) atTop
  tendsIn : Tendsto (fun x => change.symm x) (Filter.comap (fun x : ADMPoint => ‖x‖) atTop) (𝓝 0)
  coversInfinity : ∃ R : ℝ, {x : ADMPoint | R < ‖x‖} ⊆ change.target
  coeff : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ
  smooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => coeff x i j) (Metric.ball 0 radius)
  definite : ∀ x ∈ Metric.ball 0 radius, (coeff x).PosDef
  pullsBack : ∀ y ∈ change.source, ∀ v : ADMPoint,
    staticChartQuadratic coeff y v =
    staticChartQuadratic (staticPositiveMetric (fun x => -N x) h) (change y) (fderiv ℝ change y v)

/-- Smooth reflection across the finite horizon, with both asymptotic ends still open. -/
structure ReflectedStaticDouble (Ω : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) where
  carrier : Type
  [metric : MetricSpace carrier]
  [charts : ChartedSpace ADMPoint carrier]
  [manifold : IsManifold 𝓘(ℝ,ADMPoint) ∞ carrier]
  [bundle : RiemannianBundle (fun q : carrier => TangentSpace 𝓘(ℝ,ADMPoint) q)]
  [smoothMetric : IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint
    (fun q : carrier => TangentSpace 𝓘(ℝ,ADMPoint) q)]
  [riemannian : IsRiemannianManifold 𝓘(ℝ,ADMPoint) carrier]
  [connected : ConnectedSpace carrier]
  [countable : SecondCountableTopology carrier]
  lapse : carrier → ℝ
  smoothLapse : ContMDiff 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ℝ) 2 lapse
  lower : ∀ q, -1 < lapse q
  inc : Bool → C(↥(closure Ω), carrier)
  embedded : ∀ b, Topology.IsEmbedding (inc b)
  covers : ∀ q, ∃ b x, inc b x = q
  seam : ∀ x y, inc true x = inc false y ↔ x = y ∧ x.val ∈ frontier Ω
  signed : ∀ b x, lapse (inc b x) = (if b then 1 else -1) * N x.val
  side : Bool → OpenPartialHomeomorph carrier ADMPoint
  source : ∀ b, (side b).source = {q | 0 < (if b then 1 else -1) * lapse q}
  target : ∀ b, (side b).target = Ω
  inverseOnSide : ∀ b (x : ADMPoint) (hx : x ∈ Ω), (side b).symm x = inc b ⟨x, subset_closure hx⟩
  smoothSide : ∀ b, ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ (side b) (side b).source
  smoothInverse : ∀ b, ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ (side b).symm (side b).target
  sideMetric : ∀ b, ∀ x ∈ Ω, riemannianEndCoeffs (side b).symm x =
    staticPositiveMetric (fun y => (if b then 1 else -1) * N y) h x
  scalarFlat : ∀ e ∈ atlas ADMPoint carrier, ∀ x ∈ e.target, spatialScalarCurvature (riemannianEndCoeffs e.symm) x = 0
  lapseEquation : ∀ e : OpenPartialHomeomorph ADMPoint carrier,
    ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ e e.source →
    ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ e.symm e.target →
    ∀ x ∈ e.source, lapse (e x) ≠ 0 → staticWeightedLapseDivergence (riemannianEndCoeffs e) (lapse ∘ e) x = 0

attribute [instance] ReflectedStaticDouble.metric ReflectedStaticDouble.charts ReflectedStaticDouble.manifold
  ReflectedStaticDouble.bundle ReflectedStaticDouble.smoothMetric ReflectedStaticDouble.riemannian
  ReflectedStaticDouble.connected ReflectedStaticDouble.countable

end NoHair


