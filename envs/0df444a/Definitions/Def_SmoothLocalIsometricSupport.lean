-- Prove2me | Definitions.Def_SmoothLocalIsometricSupport
-- name    : SmoothLocalIsometricSupport
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T02:07:14.705065+00:00
-- url     : https://prove2.me/theorems/7906d979-558a-408d-ba4d-12b80f6e7cb3
-- title:
--   Supporting definitions for the local isometric-immersion obstruction
-- statement:
--   This bundle collects the definitions used by the statements of the intermediate results in the proof that a smooth metric exists on $(-1,1)^2$ with no local isometric immersion into $\mathbb R^3$ near the origin.
--
--   It contains: the coordinate calculus on $\mathbb R^2$ (coordinate partial derivatives and iterated partials); metric fields and their Christoffel symbols, covariant Hessian, Gaussian curvature and second fundamental form; the Darboux quantities $E=\det g\,(1-|dz|_g^2)$, $q=H_{xy}/H_{yy}$ and $G=E/H_{yy}^2$; the model curvature $\kappa(x^2-h(y))$ on the model square $[-3,3]^2$; the patch perturbation space and admissible and bounded admissible heights; the flow chart of $\partial_x-q\partial_y$ used on the caps and its coefficients; the directed multiplier weights; sheared coordinates, the oscillating pulse and the test metrics; the recursive Taylor comparison polynomial; the accumulating disks and oriented patches, and the assembled counterexample data.
--
--   **Formalization Note.** The bundle is the closure of these statements under dependence and so includes the supporting lemmas those definitions cite in their bodies, the few typeclass instances the development declares, and four compatibility lemmas (`OAI.ite_eq_left`, `OAI.ite_eq_right`, `OAI.dite_eq_left`, `OAI.dite_eq_right`) for names present in upstream's Lean 4.34.1 but absent on Lean v4.33.1. Upstream `private` markers are removed so that names resolve across the split, and the namespaces used by the development are registered at the start of the file. It imports `Def_IsometricImmersion` for the definitions in the platform's statement of the target. The mathematics and code are OpenAI's (`openai/math`, Apache License 2.0).
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0); Sections 2-5

import Mathlib
import Definitions.Def_IsometricImmersion

set_option linter.all false

namespace OAI
namespace SmoothLocal
end SmoothLocal
namespace SmoothLocal.Analytic
end SmoothLocal.Analytic
namespace SmoothLocal.DriftAlgebra
end SmoothLocal.DriftAlgebra
namespace SmoothLocal.Flow
end SmoothLocal.Flow
namespace SmoothLocal.Flow.Reflection
end SmoothLocal.Flow.Reflection
namespace SmoothLocal.Geometry
end SmoothLocal.Geometry
namespace SmoothLocal.Geometry.CoordinateBound
end SmoothLocal.Geometry.CoordinateBound
namespace SmoothLocal.Geometry.HessianCalculus
end SmoothLocal.Geometry.HessianCalculus
namespace SmoothLocal.Geometry.LowQuotient
end SmoothLocal.Geometry.LowQuotient
namespace SmoothLocal.HighEquation
end SmoothLocal.HighEquation
namespace SmoothLocal.Hyperbolic
end SmoothLocal.Hyperbolic
namespace SmoothLocal.Model
end SmoothLocal.Model
namespace SmoothLocal.ODE
end SmoothLocal.ODE
namespace SmoothLocal.Perturbation
end SmoothLocal.Perturbation
namespace SmoothLocal.Pulse
end SmoothLocal.Pulse
namespace SmoothLocal.Sobolev
end SmoothLocal.Sobolev
namespace SmoothLocal.Taylor
end SmoothLocal.Taylor
namespace SmoothLocal.Weighted
end SmoothLocal.Weighted
end OAI

section
namespace OAI

theorem ite_eq_left {α : Sort*} {c : Prop} {_ : Decidable c} {a b : α} (h : c) : ite c a b = a := if_pos h
theorem ite_eq_right {α : Sort*} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) : ite c a b = b := if_neg h
theorem dite_eq_left {α : Sort*} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort*} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators
open Filter

namespace SmoothLocal.Geometry

def coordPartial {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : Fin 2) (f : Coord → V) (p : Coord) : V :=
  fderiv ℝ f p (Pi.single i 1)

section Height
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {F : Coord → V} {p : Coord} {U : Set Coord}

end Height
end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Function Set
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Taylor

def normalizedTimePower (a : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  (t - a)^m / (m.factorial : ℝ)

section Composition
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end Composition
end SmoothLocal.Taylor

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped BigOperators Matrix ContDiff
namespace SmoothLocal.Geometry

abbrev MetricField := Coord → Matrix (Fin 2) (Fin 2) ℝ

def SmoothPositiveOn (g : MetricField) (U : Set Coord) : Prop :=
  (∀ i j, ContDiffOn ℝ ∞ (fun p => g p i j) U) ∧ ∀ p ∈ U, (g p).PosDef

def IsometricOn (g : MetricField) (F : Coord → Ambient) (U : Set Coord) : Prop :=
  ContDiffOn ℝ ∞ F U ∧ ∀ p ∈ U, ∀ v w : Coord,
    inner ℝ (fderiv ℝ F p v) (fderiv ℝ F p w) = v ⬝ᵥ (g p *ᵥ w)

def inverseMetric (g : MetricField) (p : Coord) := (g p)⁻¹

def christoffel (g : MetricField) (k i j : Fin 2) (p : Coord) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, inverseMetric g p k l *
    (coordPartial i (fun q => g q j l) p + coordPartial j (fun q => g q i l) p -
      coordPartial l (fun q => g q i j) p)

def covHessian (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  coordPartial i (coordPartial j z) p - ∑ k, christoffel g k i j p * coordPartial k z p

def covectorNormSq (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  ∑ i, ∑ j, inverseMetric g p i j * coordPartial i z p * coordPartial j z p

def riemann (g : MetricField) (l k i j : Fin 2) (p : Coord) : ℝ :=
  coordPartial i (christoffel g l j k) p - coordPartial j (christoffel g l i k) p +
    ∑ m, (christoffel g m j k p * christoffel g l i m p -
      christoffel g m i k p * christoffel g l j m p)

def gaussianCurvature (g : MetricField) (p : Coord) : ℝ :=
  (∑ l, g p 0 l * riemann g l 1 0 1 p) / (g p).det

def height (F : Coord → Ambient) (e : Ambient) : Coord → ℝ :=
  fun p => inner ℝ (F p) e

def secondFundamental (F : Coord → Ambient) (n : Ambient) (p : Coord) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => inner ℝ (coordPartial i (coordPartial j F) p) n

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

variable {f h : Coord → ℝ} {p : Coord} {U : Set Coord}

def coordinateDrift (q w : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 0 w p - q p * coordPartial 1 w p

def explicitDriftError (h E T J : Coord → ℝ) (p : Coord) : ℝ :=
  E p / (h p) ^ 2 * (T p - coordPartial 1 h p / h p) + J p / h p

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff BigOperators
namespace SmoothLocal.Geometry

def IsUnitNormalAt (F : Coord → Ambient) (e : Ambient) (p : Coord) : Prop :=
  inner ℝ e e = 1 ∧ ∀ v, inner ℝ (fderiv ℝ F p v) e = 0

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped Matrix BigOperators
open Set Metric

namespace SmoothLocal.Geometry

abbrev PlanarAxis := EuclideanSpace ℝ (Fin 2)

def axisRotation (a : PlanarAxis) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![a 1, a 0], ![-a 0, a 1]]

theorem exists_finite_unit_axis_net :
    ∃ axes : Finset PlanarAxis, (∀ a ∈ axes, ‖a‖ = 1) ∧
      ∀ v : PlanarAxis, ‖v‖ = 1 → ∃ a ∈ axes, dist v a < (1 / 1000 : ℝ) := by
  classical
  obtain ⟨s, hsphere, hsfinite, hcover⟩ :=
    (isCompact_sphere (0 : PlanarAxis) 1).finite_cover_balls
      (show (0 : ℝ) < 1 / 1000 by norm_num)
  refine ⟨hsfinite.toFinset, ?_, ?_⟩
  · intro a ha
    have hmem := hsphere (hsfinite.mem_toFinset.mp ha)
    simpa only [Metric.mem_sphere, dist_zero_right] using hmem
  · intro v hv
    have hvs : v ∈ sphere (0 : PlanarAxis) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hv
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hcover hvs)
    obtain ⟨has, hva⟩ := Set.mem_iUnion.mp ha
    exact ⟨a, hsfinite.mem_toFinset.mpr has, hva⟩

def orientationAxes : Finset PlanarAxis := Classical.choose exists_finite_unit_axis_net

def orientationRotations : Finset (Matrix (Fin 2) (Fin 2) ℝ) := by
  classical
  exact orientationAxes.image axisRotation

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Model
open SmoothLocal.Geometry

def squareTransition (t : ℝ) : ℝ := Real.smoothTransition (4 * t - 1)

def modelProfile (y : ℝ) : ℝ := 1 - y ^ 2 * squareTransition (y ^ 2)

def modelCurvature (kappa : ℝ) (p : Coord) : ℝ :=
  kappa * ((p 0) ^ 2 - modelProfile (p 1))

end SmoothLocal.Model

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

def coordinatePoint (x y : ℝ) : Coord :=
  x • Pi.single 0 1 + y • Pi.single 1 1

end SmoothLocal.ODE

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def matrixContinuousLinear (R : Matrix (Fin 2) (Fin 2) ℝ) : Coord →L[ℝ] Coord :=
  LinearMap.toContinuousLinearMap R.mulVecLin

@[simp] theorem matrixContinuousLinear_apply (R : Matrix (Fin 2) (Fin 2) ℝ) (v : Coord) :
    matrixContinuousLinear R v = R *ᵥ v := rfl

def affineCoordinates (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord) : Coord :=
  b + R *ᵥ q

def affinePullbackMetric (g : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) : MetricField := fun q =>
  Rᵀ * g (affineCoordinates b R q) * R

def affinePullbackImmersion (F : Coord → Ambient) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) : Coord → Ambient :=
  F ∘ affineCoordinates b R

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff BigOperators Matrix
namespace SmoothLocal.Geometry

def heightEnergy (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  (g p).det * (1 - covectorNormSq g z p)

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def edgeDistance (b : ℝ) (p : Coord) : ℝ := b - p 1

def weightPhase (lambda : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  -lambda * p 1 + I p

def directedWeight (b lambda : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  (edgeDistance b p) ^ 8 * Real.exp (weightPhase lambda I p)

def directedM (b lambda : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  -directedWeight b lambda I p

def directedN (b lambda epsilon : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  epsilon * p 0 * directedWeight b lambda I p

def multiplierT (B m n : Coord → ℝ) (p : Coord) : ℝ :=
  (coordPartial 1 m p - coordPartial 0 n p) / 2 + B p * n p

def multiplierS (A C m n : Coord → ℝ) (p : Coord) : ℝ :=
  -coordPartial 1 (fun q => A q * m q) p / 2 +
    coordPartial 0 (fun q => A q * n q) p / 2 + C p * m p

def multiplierJ (A B C m n : Coord → ℝ) (p : Coord) : ℝ :=
  -coordPartial 0 m p + B p * m p -
    coordPartial 1 (fun q => A q * n q) p + C p * n p

variable {I : Coord → ℝ} {U : Set Coord} {p : Coord}

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open scoped Matrix.Norms.Elementwise
open Filter

namespace SmoothLocal.Geometry

def iteratedCoordPartial {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List (Fin 2) → (Coord → V) → Coord → V
  | [], f => f
  | i :: is, f => coordPartial i (iteratedCoordPartial is f)

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def jetConnection (g : MetricField) (p : Coord) (a b : Fin 2) (u : Coord) : ℝ :=
  ∑ r, christoffel g r a b p * u r

def jetMixed (g : MetricField) (p : Coord) (b : ℝ) (u : Coord) : ℝ :=
  b - jetConnection g p 0 1 u

def jetYY (g : MetricField) (p : Coord) (c : ℝ) (u : Coord) : ℝ :=
  c - jetConnection g p 1 1 u

def jetEnergy (g : MetricField) (p : Coord) (u : Coord) : ℝ :=
  (g p).det - (g p 1 1 * (u 0) ^ 2 -
    (g p 0 1 + g p 1 0) * u 0 * u 1 + g p 0 0 * (u 1) ^ 2)

def jetNumerator (g : MetricField) (p : Coord) (b : ℝ) (u : Coord) : ℝ :=
  (jetMixed g p b u) ^ 2 + gaussianCurvature g p * jetEnergy g p u

def solvedDarboux (g : MetricField) (p : Coord) (b c : ℝ) (u : Coord) : ℝ :=
  jetConnection g p 0 0 u + jetNumerator g p b u / jetYY g p c u

namespace DarbouxJetCalculus

end DarbouxJetCalculus

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def forcingCoefficient (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  (1 - covectorNormSq g z p) / (2 * covHessian g z p 0 0)

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem smoothTransition_deriv_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  exact Filter.Eventually.of_forall (fun y => by
    rw [Real.smoothTransition.zero_of_nonpos hx]
    exact Real.smoothTransition.nonneg y)

theorem smoothTransition_deriv_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMax.deriv_eq_zero
  exact Filter.Eventually.of_forall (fun y => by
    rw [Real.smoothTransition.one_of_one_le hx]
    exact Real.smoothTransition.le_one y)

theorem exists_smoothTransition_derivative_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ M := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) hc.continuousOn
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x
  by_cases hx : x ≤ 0
  · rw [smoothTransition_deriv_zero_of_nonpos hx, abs_zero]
    exact le_trans zero_le_one (le_max_left _ _)
  by_cases hx1 : 1 ≤ x
  · rw [smoothTransition_deriv_zero_of_one_le hx1, abs_zero]
    exact le_trans zero_le_one (le_max_left _ _)
  have hxc : x ∈ Icc (0 : ℝ) 1 := ⟨(lt_of_not_ge hx).le, (lt_of_not_ge hx1).le⟩
  have hcx : |deriv Real.smoothTransition x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC x hxc
  exact hcx.trans (le_max_right _ _)

def transitionDerivativeBound : ℝ :=
  Classical.choose exists_smoothTransition_derivative_bound

def intervalCutoff (a b x : ℝ) : ℝ := Real.smoothTransition ((x - a) / (b - a))

def threeEdgeCutoff (l0 l1 r1 r0 a0 a1 : ℝ) (p : Coord) : ℝ :=
  intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) *
    intervalCutoff a0 a1 (p 1)

def capInnerEdge (x : ℝ) : ℝ := (-2 + min x (-3 / 2)) / 2
def capOuterEdge (x : ℝ) : ℝ := (-2 + capInnerEdge x) / 2

theorem capEdges_bounds {x : ℝ} (hx : -2 < x) :
    -2 < capOuterEdge x ∧ capOuterEdge x < capInnerEdge x ∧
      capInnerEdge x < -3 / 2 ∧ capInnerEdge x < x := by
  have hm : -2 < min x (-3 / 2 : ℝ) := lt_min hx (by norm_num)
  have hmx := min_le_left x (-3 / 2 : ℝ)
  have hmh := min_le_right x (-3 / 2 : ℝ)
  unfold capInnerEdge capOuterEdge
  dsimp only [capInnerEdge]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

def capSpatialCutoff (L R A : ℝ) : Coord → ℝ :=
  threeEdgeCutoff (capOuterEdge L) (capInnerEdge L)
    (-capInnerEdge (-R)) (-capOuterEdge (-R)) (capOuterEdge A) (capInnerEdge A)

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Model

def patchBox : Set Coord :=
  Icc (fun _ => (-(1 / 10 : ℝ))) (fun _ => (1 / 10 : ℝ))

def centralBox : Set Coord :=
  Icc (fun _ => (-(1 / 5 : ℝ))) (fun _ => (1 / 5 : ℝ))

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Geometry

def hessianQuotient (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  covHessian g z p 0 1 / covHessian g z p 1 1

def darbouxG (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  heightEnergy g z p / (covHessian g z p 1 1) ^ 2

def connectionTraceY (g : MetricField) (p : Coord) : ℝ :=
  christoffel g 0 0 1 p + christoffel g 1 1 1 p

def driftJ (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  (g p 0 0 - hessianQuotient g z p * g p 0 1) * coordPartial 1 z p -
    (g p 0 1 - hessianQuotient g z p * g p 1 1) * coordPartial 0 z p

def curvatureDriftError (g : MetricField) (z : Coord → ℝ) : Coord → ℝ :=
  explicitDriftError (fun p => covHessian g z p 1 1) (heightEnergy g z)
    (connectionTraceY g) (driftJ g z)

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord}

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def multiplierOperator (A B C u : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 0 (coordPartial 0 u) p + A p * coordPartial 1 (coordPartial 1 u) p +
    B p * coordPartial 0 u p + C p * coordPartial 1 u p

variable {A B C m n u : Coord → ℝ} {p : Coord} {U : Set Coord}

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry.LowQuotient

def bound0 (M c : ℝ) : ℝ := M / c
def bound1 (M c : ℝ) : ℝ := (M + M * bound0 M c) / c
def bound2 (M c : ℝ) : ℝ := (M + M * bound0 M c + 2 * M * bound1 M c) / c
def bound3 (M c : ℝ) : ℝ :=
  (M + M * bound0 M c + 3 * M * bound1 M c + 3 * M * bound2 M c) / c
def boundThroughThree (M c : ℝ) : ℝ := bound0 M c + bound1 M c + bound2 M c + bound3 M c

theorem bounds_nonneg {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c) :
    0 ≤ bound0 M c ∧ 0 ≤ bound1 M c ∧ 0 ≤ bound2 M c ∧ 0 ≤ bound3 M c := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp [bound0, bound1, bound2, bound3] <;> positivity

variable {U : Set Coord} {a b : Coord → ℝ} {M c : ℝ}

section SmoothQuotient
variable (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) (hU : IsOpen U)
variable (hM : 0 ≤ M) (hc : 0 < c)
variable (haB : ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U, |iteratedCoordPartial ds a p| ≤ M)
variable (hbB : ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U, |iteratedCoordPartial ds b p| ≤ M)
variable (hden : ∀ p ∈ U, c ≤ |b p|)
include ha hb hU hM hc haB hbB hden

end SmoothQuotient
end SmoothLocal.Geometry.LowQuotient

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

abbrev MetricMatrix := Matrix (Fin 2) (Fin 2) ℝ
abbrev MetricFirstJet := Fin 2 → MetricMatrix
abbrev MetricSecondJet := Fin 2 → Fin 2 → MetricMatrix

section Continuity
variable {T : Type*} [TopologicalSpace T] {t : T}
variable {G : T → MetricMatrix} {D : T → MetricFirstJet} {DD : T → MetricSecondJet}

end Continuity
end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

abbrev DarbouxState := Fin 6 → ℝ

def statePoint (w : DarbouxState) : Coord := ![w 0, w 1]
def stateGradient (w : DarbouxState) : Coord := ![w 2, w 3]

def stateEnergy (g : MetricField) (w : DarbouxState) : ℝ :=
  jetEnergy g (statePoint w) (stateGradient w)

def sixVariableP (g : MetricField) (w : DarbouxState) : ℝ :=
  solvedDarboux g (statePoint w) (w 4) (w 5) (stateGradient w)

variable {g : MetricField} {U : Set Coord}

def solutionJet (z : Coord → ℝ) (p : Coord) : DarbouxState :=
  ![p 0, p 1, coordPartial 0 z p, coordPartial 1 z p,
    coordPartial 0 (coordPartial 1 z) p, coordPartial 1 (coordPartial 1 z) p]

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def boxPoint (t s : ℝ) : Coord :=
  t • Pi.single 0 1 + s • Pi.single 1 1

def closedRectangle (tl tr sb st : ℝ) : Set Coord :=
  {p | p 0 ∈ Icc tl tr ∧ p 1 ∈ Icc sb st}

def rectangleIntegral (tl tr sb st : ℝ) (f : Coord → ℝ) : ℝ :=
  ∫ s in sb..st, ∫ t in tl..tr, f (boxPoint t s)

variable {tl tr sb st : ℝ} {f g : Coord → ℝ}

variable {U : Set Coord}

def multiplierQuadratic (A B C m n u : Coord → ℝ) (p : Coord) : ℝ :=
  multiplierT B m n p * (coordPartial 0 u p) ^ 2 +
    multiplierS A C m n p * (coordPartial 1 u p) ^ 2 +
    multiplierJ A B C m n p * coordPartial 0 u p * coordPartial 1 u p

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

def CoordinateBound (f : Coord → ℝ) (U : Set Coord) (n : ℕ) (M : ℝ) : Prop :=
  ∀ ds : List (Fin 2), ds.length ≤ n → ∀ p ∈ U, |iteratedCoordPartial ds f p| ≤ M

namespace CoordinateBound

end CoordinateBound
end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def metricFirstJet (g : MetricField) (p : Coord) : MetricFirstJet :=
  fun d i j => coordPartial d (fun q => g q i j) p

section SmoothLowerJet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {S : Set E} {G : E → MetricMatrix} {D : E → MetricFirstJet}

end SmoothLowerJet

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Matrix BigOperators

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

def heightPFirst (g : MetricField) (z : Coord → ℝ) (i : Fin 2) (p : Coord) : ℝ :=
  coordPartial i (solvedDarboux g p
    (coordPartial 0 (coordPartial 1 z) p) (coordPartial 1 (coordPartial 1 z) p))
    (fun r => coordPartial r z p)

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry SmoothLocal.ODE

def coordinateRectangle (R a b : ℝ) : Set Coord :=
  {p | p 0 ∈ Ioo (-R) R ∧ p 1 ∈ Ioo a b}

def coordinatePrimitive (B : Coord → ℝ) (p : Coord) : ℝ :=
  ∫ t in 0..p 0, B (coordinatePoint t (p 1))

variable {B : Coord → ℝ} {R a b : ℝ}

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted

def energyDensity (S v : Coord → ℝ) (p : Coord) : ℝ :=
  ((coordPartial 1 v p) ^ 2 + S p * (coordPartial 0 v p) ^ 2) / 2

variable {P S bTheta bXi v R : Coord → ℝ} {U : Set Coord} {p : Coord}

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def stateSegment (w0 w1 : DarbouxState) (sigma : ℝ) : DarbouxState :=
  (1 - sigma) • w0 + sigma • w1

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Metric

namespace SmoothLocal.Geometry

def roundRadiusSq (center p : Coord) : ℝ :=
  (p 0 - center 0) ^ 2 + (p 1 - center 1) ^ 2

def roundClosedDisk (center : Coord) (radius : ℝ) : Set Coord :=
  {p | roundRadiusSq center p ≤ radius ^ 2}

def roundOpenDisk (center : Coord) (radius : ℝ) : Set Coord :=
  {p | roundRadiusSq center p < radius ^ 2}

def euclideanPlaneCoordinates : Coord ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm

theorem euclideanPlaneCoordinates_dist_sq (p center : Coord) :
    dist (euclideanPlaneCoordinates p) (euclideanPlaneCoordinates center) ^ 2 =
      roundRadiusSq center p := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rfl

theorem roundClosedDisk_eq_preimage_closedBall (center : Coord) {radius : ℝ}
    (hr : 0 ≤ radius) :
    roundClosedDisk center radius = euclideanPlaneCoordinates ⁻¹'
      closedBall (euclideanPlaneCoordinates center) radius := by
  ext p
  change roundRadiusSq center p ≤ radius ^ 2 ↔
    dist (euclideanPlaneCoordinates p) (euclideanPlaneCoordinates center) ≤ radius
  rw [← euclideanPlaneCoordinates_dist_sq]
  exact sq_le_sq₀ dist_nonneg hr

theorem isCompact_roundClosedDisk (center : Coord) {radius : ℝ} (hr : 0 < radius) :
    IsCompact (roundClosedDisk center radius) := by
  rw [roundClosedDisk_eq_preimage_closedBall center hr.le]
  exact euclideanPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr
    (isCompact_closedBall (euclideanPlaneCoordinates center) radius)

theorem mem_frontier_roundClosedDisk_iff (center p : Coord) {radius : ℝ}
    (hr : 0 < radius) :
    p ∈ frontier (roundClosedDisk center radius) ↔ roundRadiusSq center p = radius ^ 2 := by
  rw [roundClosedDisk_eq_preimage_closedBall center hr.le]
  change p ∈ frontier (euclideanPlaneCoordinates.toHomeomorph ⁻¹'
    closedBall (euclideanPlaneCoordinates center) radius) ↔ _
  rw [← euclideanPlaneCoordinates.toHomeomorph.preimage_frontier,
    frontier_closedBall _ hr.ne']
  change dist (euclideanPlaneCoordinates p) (euclideanPlaneCoordinates center) = radius ↔ _
  rw [← sq_eq_sq₀ dist_nonneg hr.le, euclideanPlaneCoordinates_dist_sq]

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def coordinateSwapMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

def swappedMetric (g : MetricField) : MetricField :=
  affinePullbackMetric g 0 coordinateSwapMatrix

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def verticalJet {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Coord → V) : ℕ → Coord → V
  | 0 => f
  | n + 1 => coordPartial 1 (verticalJet f n)

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.ODE

def pairRectangle (R a b : ℝ) : Set (ℝ × ℝ) := Ioo (-R) R ×ˢ Ioo a b

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation

structure ChainWord where
  arity : ℕ
  order : Fin arity → ℕ

def ChainWord.prepend (w : ChainWord) : ChainWord :=
  ⟨w.arity + 1, Fin.cons 1 w.order⟩

def ChainWord.bump (w : ChainWord) (i : Fin w.arity) : ChainWord :=
  ⟨w.arity, Function.update w.order i (w.order i + 1)⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Metric Filter Function
open scoped ContDiff Topology NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def modelSquare : Set Coord := Icc (fun _ => (-3 : ℝ)) (fun _ => (3 : ℝ))

variable {q : Coord → ℝ} {U : Set Coord}

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry

def metricQuotientNumeratorBound (G : ℝ) : ℝ := G + 16 * G^2
def metricInverseJetBound (G d : ℝ) : ℝ :=
  LowQuotient.boundThroughThree (metricQuotientNumeratorBound G) d

theorem metricInverseJetBound_nonneg {G d : ℝ} (hG : 0 ≤ G) (hd : 0 < d) :
    0 ≤ metricInverseJetBound G d := by
  have hN : 0 ≤ metricQuotientNumeratorBound G := by dsimp [metricQuotientNumeratorBound]; positivity
  obtain ⟨h0, h1, h2, h3⟩ := LowQuotient.bounds_nonneg hN hd
  dsimp [metricInverseJetBound, LowQuotient.boundThroughThree]
  positivity

variable {g : MetricField} {U : Set Coord} {G d : ℝ}

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

def accumulatingScale (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

def accumulatingCenter (n : ℕ) : Coord := ![accumulatingScale n, 0]

def accumulatingRadius (n : ℕ) : ℝ := accumulatingScale n / 8

def accumulatingDisk (n : ℕ) : Set Coord :=
  roundClosedDisk (accumulatingCenter n) (accumulatingRadius n)

theorem accumulatingScale_pos (n : ℕ) : 0 < accumulatingScale n := by
  exact pow_pos (by norm_num) _

theorem accumulatingScale_le_half (n : ℕ) : accumulatingScale n ≤ (1 / 2 : ℝ) := by
  exact pow_le_of_le_one (by norm_num) (by norm_num) (Nat.succ_ne_zero n)

theorem accumulatingRadius_pos (n : ℕ) : 0 < accumulatingRadius n :=
  div_pos (accumulatingScale_pos n) (by norm_num)

theorem accumulatingDisk_isCompact (n : ℕ) : IsCompact (accumulatingDisk n) :=
  isCompact_roundClosedDisk (accumulatingCenter n) (accumulatingRadius_pos n)

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def jetXX (g : MetricField) (p : Coord) (c : ℝ) (u : Coord) : ℝ :=
  c - jetConnection g p 0 0 u

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation

def ChainWord.pair (a b : ℕ) : ChainWord := ⟨2, ![a, b]⟩
def ChainWord.triple (a b c : ℕ) : ChainWord := ⟨3, ![a, b, c]⟩

def ChainWord.children (w : ChainWord) : List ChainWord :=
  w.prepend :: List.ofFn w.bump

def topResidualWords : ℕ → List ChainWord
  | 0 => [ChainWord.triple 1 1 1]
  | m + 1 =>
      (topResidualWords m).flatMap ChainWord.children ++
        List.replicate (m + 3) (ChainWord.triple 1 1 (m + 2)) ++
        List.replicate (m + 3) (ChainWord.pair 2 (m + 2))

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.Geometry

def christoffelJetBound (G d : ℝ) : ℝ := 24 * metricInverseJetBound G d * G
def hessianJetBound (G Z d : ℝ) : ℝ := Z + 16 * christoffelJetBound G d * Z

theorem christoffelJetBound_nonneg {G d : ℝ} (hG : 0 ≤ G) (hd : 0 < d) :
    0 ≤ christoffelJetBound G d := by
  have hI := metricInverseJetBound_nonneg hG hd
  dsimp [christoffelJetBound]
  positivity

theorem hessianJetBound_nonneg {G Z d : ℝ} (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) :
    0 ≤ hessianJetBound G Z d := by
  have hΓ := christoffelJetBound_nonneg hG hd
  dsimp [hessianJetBound]
  positivity

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def ellipticRatioConstant (D c Cv M : ℝ) : ℝ :=
  2 * (1 + M) * Cv ^ 2 * (D ^ 2 + D ^ 3) ^ 2 +
    2 * D ^ 6 * M ^ 2 + 8 * D ^ 5 * M ^ 2 / c

def ellipticCutoffDerivativeConstant (c MK X : ℝ) : ℝ :=
  2 * (3 + X + (2 * transitionDerivativeBound / c) * (MK + c))

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

def roundDistance (c p : Coord) : ℝ :=
  dist (euclideanPlaneCoordinates p) (euclideanPlaneCoordinates c)

theorem roundDistance_sq (c p : Coord) : roundDistance c p ^ 2 = roundRadiusSq c p :=
  euclideanPlaneCoordinates_dist_sq p c

theorem roundDistance_nonneg (c p : Coord) : 0 ≤ roundDistance c p := dist_nonneg

theorem roundDistance_continuous (c : Coord) : Continuous (roundDistance c) :=
  euclideanPlaneCoordinates.continuous.dist continuous_const

theorem frontier_roundDistance_eq (c p : Coord) {r : ℝ} (hr : 0 < r)
    (hp : p ∈ frontier (roundClosedDisk c r)) : roundDistance c p = r := by
  apply (sq_eq_sq₀ (roundDistance_nonneg c p) hr.le).mp
  rw [roundDistance_sq]
  exact (mem_frontier_roundClosedDisk_iff c p hr).mp hp

def exteriorLayerInner (n k : ℕ) : ℝ :=
  accumulatingRadius n * (1 + (3 / 4 : ℝ) * accumulatingScale k)

def exteriorLayerOuter (n k : ℕ) : ℝ :=
  accumulatingRadius n * (1 + accumulatingScale k)

def exteriorLayerMiddle (n k : ℕ) : ℝ :=
  accumulatingRadius n * (1 + (7 / 8 : ℝ) * accumulatingScale k)

def exteriorOpenLayer (n k : ℕ) : Set Coord := {p |
  exteriorLayerInner n k < roundDistance (accumulatingCenter n) p ∧
    roundDistance (accumulatingCenter n) p < exteriorLayerOuter n k}

theorem exteriorLayer_radii (n k : ℕ) :
    accumulatingRadius n < exteriorLayerInner n k ∧
      exteriorLayerInner n k < exteriorLayerMiddle n k ∧
      exteriorLayerMiddle n k < exteriorLayerOuter n k ∧
      exteriorLayerOuter n k < 2 * accumulatingRadius n := by
  have hr := accumulatingRadius_pos n
  have ha := accumulatingScale_pos k
  have hab := accumulatingScale_le_half k
  have hra := mul_pos hr ha
  unfold exteriorLayerInner exteriorLayerMiddle exteriorLayerOuter
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem exteriorOpenLayer_isOpen (n k : ℕ) : IsOpen (exteriorOpenLayer n k) :=
  (isOpen_lt continuous_const (roundDistance_continuous _)).inter
    (isOpen_lt (roundDistance_continuous _) continuous_const)

def radialLift (c : Coord) (s : ℝ) (p : Coord) : Coord := c + s • (p - c)

theorem roundDistance_radialLift (c p : Coord) (s : ℝ) :
    roundDistance c (radialLift c s p) = |s| * roundDistance c p := by
  simp only [roundDistance, radialLift, dist_eq_norm, map_add, map_smul, map_sub,
    add_sub_cancel_left, norm_smul, Real.norm_eq_abs]

def exteriorMiddleLift (n k : ℕ) (p : Coord) : Coord :=
  radialLift (accumulatingCenter n) (1 + (7 / 8 : ℝ) * accumulatingScale k) p

theorem exteriorMiddleLift_mem_layer (n k : ℕ) {p : Coord}
    (hp : p ∈ frontier (accumulatingDisk n)) :
    exteriorMiddleLift n k p ∈ exteriorOpenLayer n k := by
  have hr := frontier_roundDistance_eq (accumulatingCenter n) p (accumulatingRadius_pos n) hp
  have hs : 0 ≤ 1 + (7 / 8 : ℝ) * accumulatingScale k := by
    have := accumulatingScale_pos k
    positivity
  have hrad : roundDistance (accumulatingCenter n) (exteriorMiddleLift n k p) =
      exteriorLayerMiddle n k := by
    rw [exteriorMiddleLift, roundDistance_radialLift, abs_of_nonneg hs, hr]
    unfold exteriorLayerMiddle
    ring
  change exteriorLayerInner n k < _ ∧ _ < exteriorLayerOuter n k
  rw [hrad]
  exact ⟨(exteriorLayer_radii n k).2.1, (exteriorLayer_radii n k).2.2.1⟩

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter TopologicalSpace

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Model

def modelSquare : Set Coord := Icc (fun _ => (-3 : ℝ)) (fun _ => (3 : ℝ))

def patchCompact : Compacts Coord := ⟨patchBox, isCompact_Icc⟩

abbrev SupportedTensor :=
  ContDiffMapSupportedIn Coord (Matrix (Fin 2) (Fin 2) ℝ) ⊤ patchCompact

def symmetricSupportedSubmodule : Submodule ℝ SupportedTensor where
  carrier := {η | ∀ p i j, η p i j = η p j i}
  zero_mem' := by
    change ∀ p i j, (0 : SupportedTensor) p i j = (0 : SupportedTensor) p j i
    intros
    rfl
  add_mem' := by
    intro η θ hη hθ p i j
    change η p i j + θ p i j = η p j i + θ p j i
    rw [hη p i j, hθ p i j]
  smul_mem' := by
    intro a η hη p i j
    change a * η p i j = a * η p j i
    rw [hη p i j]

abbrev SymmetricPerturbation := symmetricSupportedSubmodule

def perturbationTensor (η : SymmetricPerturbation) : MetricField := η.val

def perturbedMetric (g0 : MetricField) (η : SymmetricPerturbation) : MetricField :=
  g0 + perturbationTensor η

def metricPatchSet (g0 : MetricField) (kappa : ℝ) : Set SymmetricPerturbation :=
  {η | (∀ p ∈ modelSquare, (perturbedMetric g0 η p).PosDef) ∧
    ∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 η) p < -kappa / 2}

end SmoothLocal.Perturbation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def qToPStateIndex (i : Fin 6) : Fin 6 := ![1, 0, 3, 2, 4, 5] i

def qToPState (w : DarbouxState) : DarbouxState := fun i => w (qToPStateIndex i)

def stateQDenominator (g : MetricField) (w : DarbouxState) : ℝ :=
  jetXX g (statePoint w) (w 5) (stateGradient w)

def sixVariableQ (g : MetricField) : DarbouxState → ℝ :=
  sixVariableP (swappedMetric g) ∘ qToPState

def qSolutionJet (z : Coord → ℝ) (p : Coord) : DarbouxState :=
  ![p 0, p 1, coordPartial 0 z p, coordPartial 1 z p,
    coordPartial 0 (coordPartial 1 z) p, coordPartial 0 (coordPartial 0 z) p]

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

def movingIntervalIntegral (left right : ℝ → ℝ) (f : Coord → ℝ) (theta : ℝ) : ℝ :=
  ∫ xi in left theta..right theta, f (coordinatePoint xi theta)

def inwardLeft (x0 theta0 speed : ℝ) (theta : ℝ) : ℝ :=
  x0 + speed * (theta - theta0)

def inwardRight (x0 theta0 speed : ℝ) (theta : ℝ) : ℝ :=
  x0 - speed * (theta - theta0)

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Model

open SmoothLocal.Geometry SmoothLocal.Weighted

def modelCoercivityMargin (g0 kappa rhoMax epsilon : ℝ) (ell : ℕ) : ℝ :=
  g0 * kappa * min (3 * ((ell : ℝ) + 1 / 2) / (4 * rhoMax)) (5 * epsilon / 16)

theorem modelCoercivityMargin_pos {g0 kappa rhoMax epsilon : ℝ} (ell : ℕ)
    (hg0 : 0 < g0) (hkappa : 0 < kappa) (hrho : 0 < rhoMax) (heps : 0 < epsilon) :
    0 < modelCoercivityMargin g0 kappa rhoMax epsilon ell := by
  have hell : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
  unfold modelCoercivityMargin
  positivity

end SmoothLocal.Model

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Geometry

def riemannFirstBound (G d : ℝ) : ℝ :=
  2 * christoffelJetBound G d + 8 * (christoffelJetBound G d)^2
def curvatureNumeratorFirstBound (G d : ℝ) : ℝ := 4 * G * riemannFirstBound G d
def curvatureFirstBound (G d : ℝ) : ℝ :=
  curvatureNumeratorFirstBound G d / d +
    (curvatureNumeratorFirstBound G d + 16 * G^2 * (curvatureNumeratorFirstBound G d / d)) / d

theorem riemannFirstBound_nonneg {G d : ℝ} (hG : 0 ≤ G) (hd : 0 < d) :
    0 ≤ riemannFirstBound G d := by
  have hΓ := christoffelJetBound_nonneg hG hd
  dsimp [riemannFirstBound]; positivity

theorem curvatureFirstBound_nonneg {G d : ℝ} (hG : 0 ≤ G) (hd : 0 < d) :
    0 ≤ curvatureFirstBound G d := by
  have hR := riemannFirstBound_nonneg hG hd
  dsimp [curvatureFirstBound, curvatureNumeratorFirstBound]; positivity

variable {g : MetricField} {U : Set Coord} {G d : ℝ}

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def threeEdgeDerivativeConstant (l0 l1 r1 r0 a0 a1 : ℝ) : ℝ :=
  transitionDerivativeBound / (l1 - l0) + transitionDerivativeBound / (r0 - r1) +
    transitionDerivativeBound / (a1 - a0)

variable {U : Set Coord} {K G1 B C u f : Coord → ℝ}
  {l0 l1 r1 r0 a0 a1 b c MK g0 M : ℝ}

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def directedGradientEnergy (chi I u : Coord → ℝ) (edge lambda : ℝ) (p : Coord) : ℝ :=
  chi p * directedWeight edge lambda I p * ((coordPartial 0 u p)^2 + (coordPartial 1 u p)^2)

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

theorem accumulatingDisk_frontier_isCompact (n : ℕ) :
    IsCompact (frontier (accumulatingDisk n)) := by
  apply (accumulatingDisk_isCompact n).of_isClosed_subset isClosed_frontier
  simpa only [(accumulatingDisk_isCompact n).isClosed.closure_eq] using
    (frontier_subset_closure : frontier (accumulatingDisk n) ⊆ closure (accumulatingDisk n))

theorem exists_finite_disk_boundary_net (n k : ℕ) :
    ∃ s : Finset Coord, (∀ p ∈ s, p ∈ frontier (accumulatingDisk n)) ∧
      ∀ p ∈ frontier (accumulatingDisk n), ∃ q ∈ s, dist p q < accumulatingScale k := by
  classical
  obtain ⟨s, hsfront, hsfin, hcover⟩ :=
    (accumulatingDisk_frontier_isCompact n).finite_cover_balls (accumulatingScale_pos k)
  refine ⟨hsfin.toFinset, ?_, ?_⟩
  · intro p hp
    exact hsfront (hsfin.mem_toFinset.mp hp)
  · intro p hp
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (hcover hp)
    obtain ⟨hqs, hpq⟩ := Set.mem_iUnion.mp hq
    exact ⟨q, hsfin.mem_toFinset.mpr hqs, hpq⟩

def diskBoundaryNet (n k : ℕ) : Finset Coord :=
  Classical.choose (exists_finite_disk_boundary_net n k)

theorem diskBoundaryNet_mem_frontier (n k : ℕ) {p : Coord} (hp : p ∈ diskBoundaryNet n k) :
    p ∈ frontier (accumulatingDisk n) :=
  (Classical.choose_spec (exists_finite_disk_boundary_net n k)).1 p hp

def exteriorCenterNet (n k : ℕ) : Finset Coord := by
  classical
  exact (diskBoundaryNet n k).image (exteriorMiddleLift n k)

theorem exteriorCenterNet_mem_layer (n k : ℕ) {p : Coord} (hp : p ∈ exteriorCenterNet n k) :
    p ∈ exteriorOpenLayer n k := by
  classical
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  exact exteriorMiddleLift_mem_layer n k (diskBoundaryNet_mem_frontier n k hq)

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

def axisBump (a t : ℝ) : ℝ := expNegInvGlue (a ^ 2 - t ^ 2)

theorem axisBump_contDiff (a : ℝ) : ContDiff ℝ ∞ (axisBump a) :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

theorem axisBump_zero {a t : ℝ} (ha : 0 ≤ a) (ht : a ≤ |t|) : axisBump a t = 0 := by
  have hs : a ^ 2 ≤ |t| ^ 2 := (sq_le_sq₀ ha (abs_nonneg t)).mpr ht
  exact expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr (by simpa only [sq_abs] using hs))

theorem axisBump_support_bound {a t : ℝ} (ha : 0 < a) (ht : axisBump a t ≠ 0) :
    |t| < a := by
  by_contra h
  exact ht (axisBump_zero ha.le (le_of_not_gt h))

theorem axisBump_tsupport_subset {a : ℝ} (ha : 0 < a) :
    tsupport (axisBump a) ⊆ Icc (-a) a := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  exact ⟨(abs_lt.mp (axisBump_support_bound ha ht)).1.le,
    (abs_lt.mp (axisBump_support_bound ha ht)).2.le⟩

theorem axisBump_hasCompactSupport {a : ℝ} (ha : 0 < a) : HasCompactSupport (axisBump a) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (axisBump_tsupport_subset ha)

def temporalCutoff : ℝ → ℝ := axisBump (1 / 2)

def shearCoordinates (q0 : ℝ) (p : Coord) : Coord := ![p 0, p 1 + q0 * p 0]
def inverseShearCoordinates (q0 : ℝ) (p : Coord) : Coord := ![p 0, p 1 - q0 * p 0]
def inverseShearMatrix (q0 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; -q0, 1]
def thetaCovector (q0 : ℝ) : Coord := ![q0, 1]

def pulseScalar (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) : ℝ :=
  (1 / tau ^ N) * axisBump a (p 0) * temporalCutoff (tau * p 1 / delta) *
    Real.cos (tau * p 0)

def pulseTensor (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) : MetricField := fun p i j =>
  pulseScalar a N delta tau (shearCoordinates q0 p) * thetaCovector q0 i * thetaCovector q0 j

def testMetric (gStar : MetricField) (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) : MetricField :=
  gStar + pulseTensor q0 a N delta tau

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def qFirstCoefficient (g : MetricField) (i : Fin 6) (w : DarbouxState) : ℝ :=
  fderiv ℝ (sixVariableQ g) w (Pi.single i 1)

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

def movingEnergy (xl xr theta0 speed : ℝ) (S v : Coord → ℝ) : ℝ → ℝ :=
  movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed)
    (energyDensity S v)

def movingSourceNorm (xl xr theta0 speed : ℝ) (R : Coord → ℝ) (theta : ℝ) : ℝ :=
  Real.sqrt (movingIntervalIntegral (inwardLeft xl theta0 speed)
    (inwardRight xr theta0 speed) (fun p => R p ^ 2) theta)

variable {P S bTheta bXi v R : Coord → ℝ} {radius lo hi xl xr theta0 speed theta : ℝ}

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Model
open SmoothLocal.Geometry SmoothLocal.Weighted

def modelPrincipalRemainderBound (ell : ℕ) (R MG : ℝ) : ℝ :=
  ((ell : ℝ) + 1 / 2 + R / 2) * MG

def modelPrincipalRadius (g0 kappa rhoMax epsilon R MG : ℝ) (ell : ℕ) : ℝ :=
  min (kappa / 8) (modelCoercivityMargin g0 kappa rhoMax epsilon ell /
    (2 * (modelPrincipalRemainderBound ell R MG + 1)))

theorem modelPrincipalRemainderBound_nonneg (ell : ℕ) {R MG : ℝ}
    (hR : 0 ≤ R) (hMG : 0 ≤ MG) : 0 ≤ modelPrincipalRemainderBound ell R MG := by
  unfold modelPrincipalRemainderBound
  positivity

theorem modelPrincipalRadius_pos (ell : ℕ) {g0 kappa rhoMax epsilon R MG : ℝ}
    (hg0 : 0 < g0) (hkappa : 0 < kappa) (hrho : 0 < rhoMax) (heps : 0 < epsilon)
    (hR : 0 ≤ R) (hMG : 0 ≤ MG) :
    0 < modelPrincipalRadius g0 kappa rhoMax epsilon R MG ell := by
  have hmu := modelCoercivityMargin_pos ell hg0 hkappa hrho heps
  have hM := modelPrincipalRemainderBound_nonneg ell hR hMG
  unfold modelPrincipalRadius
  positivity

end SmoothLocal.Model

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

abbrev OrientationLabel := {R : Matrix (Fin 2) (Fin 2) ℝ // R ∈ orientationRotations}

def orientationLabelCode (R : OrientationLabel) : ℕ :=
  (Fintype.equivFin OrientationLabel R).val

def orientedLayerIndex (k : ℕ) (R : OrientationLabel) : ℕ :=
  Nat.pair k (orientationLabelCode R)

def orientedExteriorCenters (n k : ℕ) (R : OrientationLabel) : Finset Coord :=
  exteriorCenterNet n (orientedLayerIndex k R)

theorem orientedExteriorCenters_mem_layer (n k : ℕ) (R : OrientationLabel)
    {p : Coord} (hp : p ∈ orientedExteriorCenters n k R) :
    p ∈ exteriorOpenLayer n (orientedLayerIndex k R) :=
  exteriorCenterNet_mem_layer n (orientedLayerIndex k R) hp

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def metricInShearCoordinates (g : MetricField) (q0 : ℝ) : MetricField :=
  affinePullbackMetric g 0 (inverseShearMatrix q0)

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem axisBump_derivative_bound_exists {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ∃ C : ℝ, ∀ t, ‖iteratedFDeriv ℝ k (axisBump a) t‖ ≤ C :=
  ((axisBump_contDiff a).continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).bounded_above_of_compact_support
    ((axisBump_hasCompactSupport ha).iteratedFDeriv k)

def axisBumpDerivativeBound (a : ℝ) (ha : 0 < a) (k : ℕ) : ℝ :=
  1 + |Classical.choose (axisBump_derivative_bound_exists ha k)|

def xiCLM : Coord →L[ℝ] ℝ := ContinuousLinearMap.proj 0
def thetaCLM (q0 : ℝ) : Coord →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 1 + q0 • ContinuousLinearMap.proj 0

def pulseScaleBound (q0 delta : ℝ) : ℝ :=
  1 + ‖xiCLM‖ + |delta⁻¹| * ‖thetaCLM q0‖

def derivativeConvolution (A B : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A i * B (k - i)

def pulseCoreDerivativeBound (a : ℝ) (ha : 0 < a) : ℕ → ℝ :=
  derivativeConvolution
    (derivativeConvolution (axisBumpDerivativeBound a ha)
      (axisBumpDerivativeBound (1 / 2) (by norm_num))) (fun _ => 1)

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def qHeightJetSegment (z0 z : Coord → ℝ) (sigma : ℝ) (p : Coord) : DarbouxState :=
  stateSegment (qSolutionJet z0 p) (qSolutionJet z p) sigma

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

def closedPatchBox : Set Coord := {x | ∀ i, x i ∈ Set.Icc (-4 : ℝ) 4}

theorem mem_closedPatchBox_iff_norm_le (x : Coord) :
    x ∈ closedPatchBox ↔ ‖x‖ ≤ 4 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  simp only [closedPatchBox, Set.mem_ofPred_eq, Set.mem_Icc, Real.norm_eq_abs, abs_le]

def closedAffineSquare (c : Coord) (scale : ℝ) (R : Matrix (Fin 2) (Fin 2) ℝ) : Set Coord :=
  affineCoordinates c (scale • R) '' closedPatchBox

theorem closedAffineSquare_dist_le (c : Coord) {scale : ℝ} (hscale : 0 ≤ scale)
    (R : Matrix (Fin 2) (Fin 2) ℝ) {p : Coord} (hp : p ∈ closedAffineSquare c scale R) :
    dist p c ≤ scale * (4 * ‖matrixContinuousLinear R‖) := by
  obtain ⟨x, hx, rfl⟩ := hp
  have hxnorm := (mem_closedPatchBox_iff_norm_le x).mp hx
  have hmap := (matrixContinuousLinear R).le_opNorm_of_le hxnorm
  calc
    dist (affineCoordinates c (scale • R) x) c = scale * ‖matrixContinuousLinear R x‖ := by
      simp only [affineCoordinates, Matrix.smul_mulVec, dist_eq_norm,
        add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale,
        matrixContinuousLinear_apply]
    _ ≤ scale * (‖matrixContinuousLinear R‖ * 4) := mul_le_mul_of_nonneg_left hmap hscale
    _ = _ := by ring

theorem finite_positive_lower_bound {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) : ∃ δ > 0, ∀ i ∈ s, δ < a i := by
  classical
  revert ha
  induction s using Finset.induction_on with
  | empty => intro ha; exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
      intro ha
      obtain ⟨δ, hδ, hδa⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      have hai := ha i (Finset.mem_insert_self i s)
      refine ⟨min (a i / 2) δ, lt_min (by positivity) hδ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      · exact lt_of_le_of_lt (min_le_right _ _) (hδa j hj)

theorem exists_finite_affine_square_scale {ι : Type*} [Fintype ι]
    (c : ι → Coord) (hc : Function.Injective c) {U : Set Coord}
    (hU : IsOpen U) (hcU : ∀ i, c i ∈ U)
    (R : Matrix (Fin 2) (Fin 2) ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ scale > 0, scale ≤ η ∧
      (∀ i, closedAffineSquare (c i) scale R ⊆ U) ∧
      Pairwise (fun i j => Disjoint (closedAffineSquare (c i) scale R)
        (closedAffineSquare (c j) scale R)) ∧
      ∀ i p, p ∈ closedAffineSquare (c i) scale R → dist p (c i) ≤ η := by
  classical
  have hballs : ∀ i, ∃ a > 0, Metric.ball (c i) a ⊆ U :=
    fun i => Metric.mem_nhds_iff.mp (hU.mem_nhds (hcU i))
  choose a ha haU using hballs
  obtain ⟨ρ, hρ, hρa⟩ := finite_positive_lower_bound Finset.univ a (by simpa using ha)
  let separation : ι × ι → ℝ := fun ij => if ij.1 = ij.2 then 1 else dist (c ij.1) (c ij.2)
  have hsep : ∀ ij ∈ (Finset.univ : Finset (ι × ι)), 0 < separation ij := by
    intro ij _
    dsimp only [separation]
    split_ifs with hij
    · norm_num
    · exact dist_pos.mpr (fun h => hij (hc h))
  obtain ⟨δ, hδ, hδsep⟩ := finite_positive_lower_bound Finset.univ separation hsep
  let t : ℝ := min ρ (min δ η) / 4
  have ht : 0 < t := by dsimp only [t]; positivity
  have htρ : t ≤ ρ / 4 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have htδ : t ≤ δ / 4 := div_le_div_of_nonneg_right
    ((min_le_right ρ (min δ η)).trans (min_le_left δ η)) (by norm_num)
  have htη : t ≤ η / 4 := div_le_div_of_nonneg_right
    ((min_le_right ρ (min δ η)).trans (min_le_right δ η)) (by norm_num)
  let scale : ℝ := t / (1 + 4 * ‖matrixContinuousLinear R‖)
  have hden : 0 < 1 + 4 * ‖matrixContinuousLinear R‖ := by positivity
  have hscale : 0 < scale := div_pos ht hden
  have hscaleeq : scale * (1 + 4 * ‖matrixContinuousLinear R‖) = t :=
    div_mul_cancel₀ t hden.ne'
  have hscalet : scale ≤ t := by
    nlinarith [mul_nonneg hscale.le (norm_nonneg (matrixContinuousLinear R))]
  have hsize : scale * (4 * ‖matrixContinuousLinear R‖) ≤ t := by nlinarith
  have hcontain (i : ι) : closedAffineSquare (c i) scale R ⊆ Metric.closedBall (c i) t := by
    intro p hp
    exact (closedAffineSquare_dist_le (c i) hscale.le R hp).trans hsize
  refine ⟨scale, hscale, by linarith, ?_, ?_, ?_⟩
  · intro i
    apply Set.Subset.trans (hcontain i)
    apply Set.Subset.trans (Metric.closedBall_subset_ball (show t < a i from by
      have := hρa i (Finset.mem_univ i)
      linarith))
    exact haU i
  · intro i j hij
    have hd : δ < dist (c i) (c j) := by
      simpa only [separation, ite_eq_right hij] using hδsep (i, j) (Finset.mem_univ (i, j))
    exact (Metric.closedBall_disjoint_closedBall (show t + t < dist (c i) (c j) by
      linarith)).mono (hcontain i) (hcontain j)
  · intro i p hp
    have := hcontain i hp
    change dist p (c i) ≤ t at this
    linarith

theorem exists_finset_affine_square_scale (s : Finset Coord) {U : Set Coord}
    (hU : IsOpen U) (hsU : ∀ c ∈ s, c ∈ U)
    (R : Matrix (Fin 2) (Fin 2) ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ scale > 0, scale ≤ η ∧
      (∀ c ∈ s, closedAffineSquare c scale R ⊆ U) ∧
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → Disjoint (closedAffineSquare c scale R)
        (closedAffineSquare d scale R)) ∧
      ∀ c ∈ s, ∀ p ∈ closedAffineSquare c scale R, dist p c ≤ η := by
  classical
  obtain ⟨scale, hscale, hscaleη, hsub, hdisj, hbound⟩ :=
    exists_finite_affine_square_scale (fun c : {c // c ∈ s} => c.val)
      Subtype.val_injective hU (fun c => hsU c.val c.property) R hη
  exact ⟨scale, hscale, hscaleη, fun c hc => hsub ⟨c, hc⟩,
    fun c hc d hd hcd => hdisj (i := ⟨c, hc⟩) (j := ⟨d, hd⟩)
      (fun h => hcd (congrArg Subtype.val h)),
    fun c hc p hp => hbound ⟨c, hc⟩ p hp⟩

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def heightInShearCoordinates (z : Coord → ℝ) (q0 : ℝ) : Coord → ℝ :=
  z ∘ inverseShearCoordinates q0

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

abbrev CurvatureFirstInput := (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 2 → Fin 2 → ℝ)

def actualCurvatureFirstInput (g : MetricField) (p : Coord) : CurvatureFirstInput :=
  ((fun i j => g p i j),(fun d i j => metricFirstJet g p d i j))

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def pulsePrincipalRemainderBound (a : ℝ) (ha : 0 < a) : ℝ :=
  axisBumpDerivativeBound (1/2) (by norm_num) 0 *
    (axisBumpDerivativeBound a ha 1+axisBumpDerivativeBound a ha 2)

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

def pulseStrip (a delta tau : ℝ) : Set Coord :=
  closedRectangle (-a) a (-(delta/tau)) (delta/tau)
def pulsePairRectangle (a delta tau : ℝ) : Set (ℝ × ℝ) :=
  Icc (-(delta/tau)) (delta/tau) ×ˢ Icc (-a) a
def pulsePairPoint (q : ℝ × ℝ) : Coord := boxPoint q.2 q.1
def pulseTest (a tau x : ℝ) : ℝ := axisBump a x*Real.cos (tau*x)

def pulseWeightedMoment (a delta tau : ℝ) (f : Coord → ℝ) : ℝ :=
  ∫ q in pulsePairRectangle a delta tau, f (pulsePairPoint q)*pulseTest a tau q.2
    ∂volume.prod volume

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

theorem exists_orientedPatchScale (n k : ℕ) (R : OrientationLabel) :
    ∃ scale > 0, scale ≤ accumulatingScale k ∧
      (∀ c ∈ orientedExteriorCenters n k R, closedAffineSquare c scale R.val ⊆
        exteriorOpenLayer n (orientedLayerIndex k R)) ∧
      (∀ c ∈ orientedExteriorCenters n k R, ∀ d ∈ orientedExteriorCenters n k R,
        c ≠ d → Disjoint (closedAffineSquare c scale R.val) (closedAffineSquare d scale R.val)) ∧
      ∀ c ∈ orientedExteriorCenters n k R, ∀ p ∈ closedAffineSquare c scale R.val,
        dist p c ≤ accumulatingScale k :=
  exists_finset_affine_square_scale (orientedExteriorCenters n k R)
    (exteriorOpenLayer_isOpen n (orientedLayerIndex k R))
    (fun _ hc => orientedExteriorCenters_mem_layer n k R hc) R.val (accumulatingScale_pos k)

def orientedPatchScale (n k : ℕ) (R : OrientationLabel) : ℝ :=
  Classical.choose (exists_orientedPatchScale n k R)

def orientedClosedPatch (n k : ℕ) (R : OrientationLabel) (c : Coord) : Set Coord :=
  closedAffineSquare c (orientedPatchScale n k R) R.val

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

variable {P S bTheta bXi v R : Coord → ℝ} {radius lo hi xl xr theta0 speed theta : ℝ}

def shrinkingSlab (xl xr a b speed : ℝ) : Set Coord :=
  {p | p 1 ∈ Icc a b ∧ p 0 ∈ Icc (inwardLeft xl a speed (p 1))
    (inwardRight xr a speed (p 1))}

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def scalarPulseDerivativeBound (a : ℝ) (ha : 0 < a) (delta : ℝ) (k : ℕ) : ℝ :=
  pulseCoreDerivativeBound a ha k * pulseScaleBound 0 delta ^ k

def scalarPulseFirstJetBound (a : ℝ) (ha : 0 < a) (delta : ℝ) : ℝ :=
  max (scalarPulseDerivativeBound a ha delta 0) (scalarPulseDerivativeBound a ha delta 1)

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

def capChartDomain : Set Coord := coordinateRectangle 2 (-2) 2

def capFlowHeight (Y : ℝ → ℝ → ℝ) (p : Coord) : ℝ := Y (p 1) (p 0)

def capChart (Y : ℝ → ℝ → ℝ) (p : Coord) : Coord :=
  coordinatePoint (p 0) (capFlowHeight Y p)

def capChartRho (Y : ℝ → ℝ → ℝ) (p : Coord) : ℝ :=
  1 / coordPartial 1 (capFlowHeight Y) p

variable {Y : ℝ → ℝ → ℝ}

variable {q : Coord → ℝ}

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.ODE

def PatchAdmissibleHeight (g : MetricField) (z : Coord → ℝ) : Prop :=
  ∃ U : Set Coord, IsOpen U ∧ modelSquare ⊆ U ∧ SmoothPositiveOn g U ∧
    ContDiffOn ℝ ∞ z U ∧
    (∀ p ∈ modelSquare,
      (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) ∧
    (∀ p ∈ modelSquare, 0 < heightEnergy g z p) ∧
    (∀ p ∈ modelSquare, covHessian g z p 1 1 ≠ 0) ∧
    (∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ) / 100)

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def curvatureDensity (g : MetricField) (p : Coord) : ℝ :=
  gaussianCurvature g p*(g p).det

def testDensityErrorCoefficient (C a : ℝ) (ha : 0 < a) (delta : ℝ) : ℝ :=
  pulsePrincipalRemainderBound a ha+C*scalarPulseFirstJetBound a ha delta

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def averagedQCoefficient (g : MetricField) (w0 w1 : DarbouxState) (i : Fin 6) : ℝ :=
  ∫ sigma in (0 : ℝ)..1, qFirstCoefficient g i (stateSegment w0 w1 sigma)

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise Distributions

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

def metricApproximationAccuracy (tau : ℕ) : ℝ := 1 / ((tau : ℝ)^tau)

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Filter

namespace SmoothLocal.Geometry

abbrev PatchAddress := Σ n : ℕ, Σ k : ℕ, Σ R : OrientationLabel,
  {c : Coord // c ∈ orientedExteriorCenters n k R}

instance : Countable PatchAddress := by
  classical
  let : ∀ (n k : ℕ) (R : OrientationLabel),
      Finite {c : Coord // c ∈ orientedExteriorCenters n k R} :=
    fun n k R => (orientedExteriorCenters n k R).finite_toSet.to_subtype
  infer_instance

abbrev AssemblyProfileIndex := ℕ ⊕ PatchAddress

instance assemblyProfileEncodable : Encodable AssemblyProfileIndex :=
  Encodable.ofCountable AssemblyProfileIndex

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal NNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Sobolev

def spatialJet (f : Coord → ℝ) : ℕ → Coord → ℝ
  | 0 => f
  | n + 1 => coordPartial 0 (spatialJet f n)

def SpatialSliceL2Bound {ι : Type*} (F : ι → Coord → ℝ) (theta left right : ℝ)
    (N : ℕ) (H : ℝ≥0) : Prop :=
  ∀ i n, n ≤ N → eLpNorm (fun x => spatialJet (F i) n (coordinatePoint x theta)) 2
    (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞)

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def capPullback (Y : ℝ → ℝ → ℝ) (u : Coord → ℝ) : Coord → ℝ := fun p => u (capChart Y p)

def capChartSigma (Y : ℝ → ℝ → ℝ) (p : Coord) : ℝ :=
  -coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p /
    (coordPartial 1 (capFlowHeight Y) p) ^ 3

def capTransportA (Y : ℝ → ℝ → ℝ) (a : Coord → ℝ) (p : Coord) : ℝ :=
  capPullback Y a p * (capChartRho Y p) ^ 2

def capTransportC (Y : ℝ → ℝ → ℝ) (a C0 : Coord → ℝ) (p : Coord) : ℝ :=
  capPullback Y a p * capChartSigma Y p + capPullback Y C0 p * capChartRho Y p

variable {Y : ℝ → ℝ → ℝ} {u q : Coord → ℝ} {U : Set Coord} {p : Coord}

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def heightOriginalA (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  gaussianCurvature g p * darbouxG g z p

def heightOriginalB (g : MetricField) (z : Coord → ℝ) (ell : ℕ) (p : Coord) : ℝ :=
  -heightPFirst g z 0 p - 2 * (ell : ℝ) * coordPartial 1 (hessianQuotient g z) p

def heightOriginalC0 (g : MetricField) (z : Coord → ℝ) (ell : ℕ) (p : Coord) : ℝ :=
  coordinateDrift (hessianQuotient g z) (hessianQuotient g z) p -
    hessianQuotient g z p * heightPFirst g z 0 p - heightPFirst g z 1 p +
      (ell : ℝ) * coordPartial 1 (heightOriginalA g z) p

def heightChartA (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) : Coord → ℝ :=
  capTransportA Y (heightOriginalA g z)

def heightChartB (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (ell : ℕ) : Coord → ℝ :=
  capPullback Y (heightOriginalB g z ell)

def heightChartC (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (ell : ℕ) : Coord → ℝ :=
  capTransportC Y (heightOriginalA g z) (heightOriginalC0 g z ell)

def heightChartG1 (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : Coord) : ℝ :=
  capPullback Y (darbouxG g z) p * (capChartRho Y p) ^ 2

def heightChartRemainder (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ)
    (ell : ℕ) (p : Coord) : ℝ :=
  (capPullback Y (curvatureDriftError g z) p - capPullback Y (coordPartial 1 (darbouxG g z)) p) /
      (capPullback Y (darbouxG g z) p * capChartRho Y p) -
    (2 * (ell : ℝ) + 1) * capChartSigma Y p / (capChartRho Y p) ^ 2

variable {g : MetricField} {z u : Coord → ℝ} {U : Set Coord} {p : Coord} {Y : ℝ → ℝ → ℝ}

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal NNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

def spatialFirstJet (z : Coord → ℝ) (i : Fin 2) : Coord → ℝ := coordPartial i z

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def capOverlapThreshold (kappa c1 D : ℝ) : ℝ := min c1 (kappa / (D + 1))

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def modelOpenSquare : Set Coord := coordinateRectangle 3 (-3) 3

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def horizontalJet {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Coord → V) : ℕ → Coord → V
  | 0 => f
  | n + 1 => coordPartial 0 (horizontalJet f n)

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def firstJetPairRemainder (g : MetricField) (z : Coord → ℝ) (n : ℕ) (p : Coord) : ℝ :=
  coordPartial 1 (heightPFirst g z 0) p * coordPartial 0 (verticalJet z n) p +
  coordPartial 1 (heightPFirst g z 1) p * coordPartial 1 (verticalJet z n) p

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

def heightEnergyJetBound (G Z : ℝ) : ℝ := 16 * G^2 + 256 * G * Z^2
def darbouxGJetBound (G Z d c : ℝ) : ℝ :=
  LowQuotient.boundThroughThree
    (heightEnergyJetBound G Z + 8 * (hessianJetBound G Z d)^2) (c^2)

theorem heightEnergyJetBound_nonneg {G Z : ℝ} (hG : 0 ≤ G) : 0 ≤ heightEnergyJetBound G Z := by
  dsimp [heightEnergyJetBound]; positivity

theorem darbouxGJetBound_nonneg {G Z d c : ℝ} (hG : 0 ≤ G) (hc : 0 < c) :
    0 ≤ darbouxGJetBound G Z d c := by
  have hE := heightEnergyJetBound_nonneg (Z := Z) hG
  obtain ⟨h0, h1, h2, h3⟩ := LowQuotient.bounds_nonneg
    (show 0 ≤ heightEnergyJetBound G Z + 8 * (hessianJetBound G Z d)^2 by positivity) (pow_pos hc 2)
  dsimp [darbouxGJetBound, LowQuotient.boundThroughThree]
  positivity

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def capSpatialDerivativeConstant (L R A : ℝ) : ℝ :=
  threeEdgeDerivativeConstant (capOuterEdge L) (capInnerEdge L)
    (-capInnerEdge (-R)) (-capOuterEdge (-R)) (capOuterEdge A) (capInnerEdge A)

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def directedPrincipalBound (ell : ℕ) (epsilon R MAs MAt : ℝ) : ℝ :=
  ((ell : ℝ) + 1 / 2) * MAs + epsilon * R * MAt / 2

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

abbrev QFirstInput := CurvatureFirstInput × DarbouxState

def qFirstBundle (g : MetricField) (w : DarbouxState) : QFirstInput :=
  (actualCurvatureFirstInput g (statePoint w),w)

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def coordinateChainTerm (g : MetricField) (z : Coord → ℝ) (w : ChainWord) (p : Coord) : ℝ :=
  iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z p)
    (fun i => verticalJet (solutionJet z) (w.order i) p)

def coordinateChainSum (g : MetricField) (z : Coord → ℝ) (ws : List ChainWord) (p : Coord) : ℝ :=
  (ws.map (fun w => coordinateChainTerm g z w p)).sum

def actualHighRemainder (g : MetricField) (z : Coord → ℝ) (m : ℕ) (p : Coord) : ℝ :=
  coordinateChainSum g z (topResidualWords m) p +
    (m + 3 : ℝ) * firstJetPairRemainder g z (m + 2) p

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

def heightQuotientJetBound (G Z d c : ℝ) : ℝ :=
  LowQuotient.boundThroughThree (hessianJetBound G Z d) c
def heightAlongDJetBound (G Z d c : ℝ) : ℝ :=
  christoffelJetBound G d + 16 * heightQuotientJetBound G Z d c * christoffelJetBound G d +
    64 * (heightQuotientJetBound G Z d c)^2 * christoffelJetBound G d
def heightEnergyFirstQuotientBound (G Z d c : ℝ) : ℝ :=
  LowQuotient.boundThroughThree (32 * G * Z + hessianJetBound G Z d) c
def heightPFirstBound (G Z d c : ℝ) : ℝ :=
  heightAlongDJetBound G Z d c + 2 * curvatureFirstBound G d *
    (heightEnergyFirstQuotientBound G Z d c + 8 * darbouxGJetBound G Z d c * christoffelJetBound G d)

theorem heightQuotientJetBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightQuotientJetBound G Z d c := by
  obtain ⟨h0, h1, h2, h3⟩ := LowQuotient.bounds_nonneg (hessianJetBound_nonneg hG hZ hd) hc
  dsimp [heightQuotientJetBound, LowQuotient.boundThroughThree]
  positivity

theorem heightAlongDJetBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightAlongDJetBound G Z d c := by
  have hq := heightQuotientJetBound_nonneg hG hZ hd hc
  have hΓ := christoffelJetBound_nonneg hG hd
  dsimp [heightAlongDJetBound]; positivity

theorem heightEnergyFirstQuotientBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightEnergyFirstQuotientBound G Z d c := by
  have hH := hessianJetBound_nonneg hG hZ hd
  obtain ⟨h0, h1, h2, h3⟩ := LowQuotient.bounds_nonneg (show 0 ≤ 32 * G * Z + hessianJetBound G Z d by positivity) hc
  dsimp [heightEnergyFirstQuotientBound, LowQuotient.boundThroughThree]
  positivity

theorem heightPFirstBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) : 0 ≤ heightPFirstBound G Z d c := by
  have hA := heightAlongDJetBound_nonneg hG hZ hd hc
  have hK := curvatureFirstBound_nonneg hG hd
  have hJ := heightEnergyFirstQuotientBound_nonneg hG hZ hd hc
  have hD := darbouxGJetBound_nonneg (Z := Z) (d := d) hG hc
  have hΓ := christoffelJetBound_nonneg hG hd
  dsimp [heightPFirstBound]; positivity

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def directedWeightJetBudget (D M lambda : ℝ) : ℝ := 16 + 3*D + 2*D*(M+lambda)

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Model

theorem exists_directed_parameters (ell : ℕ)
    {kappa cG rhoMax MG MI MB Mr MA MAs MAt MG1 D : ℝ}
    (hk : 0 < kappa) (hcG : 0 < cG) (hrho : 0 < rhoMax)
    (hMG : 0 ≤ MG) (hMI : 0 ≤ MI) (hMB : 0 ≤ MB) (hMr : 0 ≤ Mr)
    (hMA : 0 ≤ MA) (hMAs : 0 ≤ MAs) (hMAt : 0 ≤ MAt) (hMG1 : 0 ≤ MG1) (hD : 0 ≤ D) :
    ∃ epsilon lambda c1 : ℝ,
      0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧
      epsilon * 2 * ((1 : ℝ) / 100) ≤ ((ell : ℝ) + 1 / 2) / rhoMax ∧
      2 * (MI + epsilon + epsilon * 2 * MB) ≤ lambda ∧
      (MI + 1 + 2 * MB) / 2 + Mr ≤ lambda / 8 ∧
      4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 * epsilon^2 * MA ≤ 1 / 8 ∧
      (4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 * epsilon^2) / lambda ≤
        modelCoercivityMargin cG kappa rhoMax epsilon ell / 8 ∧
      directedPrincipalBound ell epsilon 2 MAs MAt + modelCoercivityMargin cG kappa rhoMax epsilon ell / 2 ≤
        lambda * (cG * modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell) / 4 ∧
      c1 * D ≤ modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell ∧
      MG1 * c1 * (lambda * D + 8) ≤ modelCoercivityMargin cG kappa rhoMax epsilon ell / 6 := by
  let Cj := 2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)
  let L := 4 * Cj^2
  have hCj : 0 ≤ Cj := by dsimp [Cj]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbeta : 0 < ((ell : ℝ) + 1 / 2) / rhoMax := by positivity
  have hden : 0 < 8 * L * MA + 1 := by positivity
  let epsilon := min 1 (min (((ell : ℝ) + 1 / 2) / rhoMax) (1 / (8 * L * MA + 1)))
  have heps : 0 < epsilon := by dsimp [epsilon]; positivity
  have heps1 : epsilon ≤ 1 := min_le_left _ _
  have hepsbeta : epsilon ≤ ((ell : ℝ) + 1 / 2) / rhoMax :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hepsden : epsilon ≤ 1 / (8 * L * MA + 1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hcross : L * epsilon^2 * MA ≤ 1 / 8 := by
    have hm := (le_div_iff₀ hden).mp hepsden
    have hsquare : epsilon^2 ≤ epsilon := by nlinarith only [heps.le, heps1]
    have hprod := mul_le_mul_of_nonneg_left hsquare (mul_nonneg hL hMA)
    nlinarith only [hm, hprod, heps.le]
  have hqbudget : epsilon * 2 * ((1 : ℝ) / 100) ≤ ((ell : ℝ) + 1 / 2) / rhoMax := by
    have hh : epsilon * 2 * ((1 : ℝ) / 100) ≤ epsilon := by linarith only [heps.le]
    exact hh.trans hepsbeta
  let margin := modelCoercivityMargin cG kappa rhoMax epsilon ell
  let delta := modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell
  let alpha := cG * delta
  have hmargin : 0 < margin := modelCoercivityMargin_pos ell hcG hk hrho heps
  have hdelta : 0 < delta := modelPrincipalRadius_pos ell hcG hk hrho heps (by norm_num) hMG
  have halpha : 0 < alpha := mul_pos hcG hdelta
  let T0 := 2 * (MI + 1 + 2 * MB)
  let E0 := (MI + 1 + 2 * MB) / 2 + Mr
  let P0 := ((ell : ℝ) + 1 / 2) * MAs + MAt
  have hT0 : 0 ≤ T0 := by dsimp [T0]; positivity
  have hE0 : 0 ≤ E0 := by dsimp [E0]; positivity
  have hP0 : 0 ≤ P0 := by dsimp [P0]; positivity
  let lambda := 1 + T0 + 8 * E0 + 8 * L * epsilon^2 / margin + 4 * (P0 + margin / 2) / alpha
  have hLterm : 0 ≤ 8 * L * epsilon^2 / margin := by positivity
  have hFterm : 0 ≤ 4 * (P0 + margin / 2) / alpha := by positivity
  have hlambda : 0 < lambda := by dsimp [lambda]; linarith only [hT0, hE0, hLterm, hFterm]
  have hTlambda : T0 ≤ lambda := by dsimp [lambda]; linarith only [hE0, hLterm, hFterm]
  have hElambda : 8 * E0 ≤ lambda := by dsimp [lambda]; linarith only [hT0, hLterm, hFterm]
  have hLlambda : 8 * L * epsilon^2 / margin ≤ lambda := by dsimp [lambda]; linarith only [hT0, hE0, hFterm]
  have hFlambda : 4 * (P0 + margin / 2) / alpha ≤ lambda := by dsimp [lambda]; linarith only [hT0, hE0, hLterm]
  have hTbudget : 2 * (MI + epsilon + epsilon * 2 * MB) ≤ lambda := by
    have hp := mul_le_mul_of_nonneg_right heps1 (show 0 ≤ 2 * MB by positivity)
    have hh : 2 * (MI + epsilon + epsilon * 2 * MB) ≤ T0 := by dsimp [T0]; nlinarith only [hp, heps1]
    exact hh.trans hTlambda
  have hEbudget : E0 ≤ lambda / 8 := by linarith only [hElambda]
  have hloss : L * epsilon^2 / lambda ≤ margin / 8 := by
    have hh := (div_le_iff₀ hmargin).mp hLlambda
    apply (div_le_iff₀ hlambda).mpr
    nlinarith only [hh]
  have hprincipal : directedPrincipalBound ell epsilon 2 MAs MAt ≤ P0 := by
    have hh := mul_le_mul_of_nonneg_right heps1 hMAt
    dsimp [directedPrincipalBound, P0]
    nlinarith only [hh]
  have hfar : directedPrincipalBound ell epsilon 2 MAs MAt + margin / 2 ≤ lambda * alpha / 4 := by
    have hh := (div_le_iff₀ halpha).mp hFlambda
    nlinarith only [hh, hprincipal]
  have hD1 : 0 < D + 1 := by linarith only [hD]
  have hstripden : 0 < 6 * (MG1 + 1) * (lambda * D + 8) := by positivity
  let c1 := min (delta / (D + 1)) (margin / (6 * (MG1 + 1) * (lambda * D + 8)))
  have hc1 : 0 < c1 := by dsimp [c1]; positivity
  have hc1delta : c1 ≤ delta / (D + 1) := min_le_left _ _
  have hc1strip : c1 ≤ margin / (6 * (MG1 + 1) * (lambda * D + 8)) := min_le_right _ _
  have hnearstrip : c1 * D ≤ delta := by
    have hh := (le_div_iff₀ hD1).mp hc1delta
    nlinarith only [hh, hc1.le]
  have hstrip : MG1 * c1 * (lambda * D + 8) ≤ margin / 6 := by
    have hh := (le_div_iff₀ hstripden).mp hc1strip
    have hfac : 0 ≤ c1 * (lambda * D + 8) := by positivity
    have hbase : MG1 * c1 * (lambda * D + 8) ≤ (MG1 + 1) * c1 * (lambda * D + 8) := by
      nlinarith only [hfac]
    have hfull : (MG1 + 1) * c1 * (lambda * D + 8) ≤ margin / 6 := by nlinarith only [hh]
    exact hbase.trans hfull
  exact ⟨epsilon, lambda, c1, heps, heps1, hlambda, hc1, hqbudget, hTbudget,
    hEbudget, hcross, hloss, hfar, hnearstrip, hstrip⟩

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.ODE

def heightDriftErrorBound (G Z d c : ℝ) : ℝ :=
  heightEnergyJetBound G Z / c^2 *
    (2 * christoffelJetBound G d + hessianJetBound G Z d / c) +
    ((202 / 100 : ℝ) * (G + Z)^2) / c

theorem heightDriftErrorBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightDriftErrorBound G Z d c := by
  have hE := heightEnergyJetBound_nonneg (Z := Z) hG
  have hΓ := christoffelJetBound_nonneg hG hd
  have hH := hessianJetBound_nonneg hG hZ hd
  dsimp [heightDriftErrorBound]; positivity

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def directedQuadraticCostConstant (D M lambda S MI : ℝ) : ℝ :=
  (2+8*M)*directedWeightJetBudget D M lambda*Real.exp (lambda*S+MI)

def directedDefectCostConstant (D M lambda S MI c2 : ℝ) : ℝ :=
  c2*D*Real.exp (lambda*S+MI) + directedQuadraticCostConstant D M lambda S MI

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def flowCoordinateBound (M : ℝ) : ℝ :=
  4 + Real.exp (2 * M) + 2 * M + M * Real.exp (2 * M) + 2 * M * Real.exp (4 * M) +
    (4 * M + 2 * M^2) + (2 * M + M^2) * Real.exp (2 * M) +
    (M + 2 * M^2) * Real.exp (4 * M) + (2 * M + 8 * M^2) * Real.exp (6 * M)

theorem flowCoordinateBound_dominates {M : ℝ} (hM : 0 ≤ M) :
    3 ≤ flowCoordinateBound M ∧ 1 ≤ flowCoordinateBound M ∧
    Real.exp (2 * M) ≤ flowCoordinateBound M ∧ 2 * M ≤ flowCoordinateBound M ∧
    M * Real.exp (2 * M) ≤ flowCoordinateBound M ∧ 2 * M * Real.exp (4 * M) ≤ flowCoordinateBound M ∧
    4 * M + 2 * M^2 ≤ flowCoordinateBound M ∧
    (2 * M + M^2) * Real.exp (2 * M) ≤ flowCoordinateBound M ∧
    (M + 2 * M^2) * Real.exp (4 * M) ≤ flowCoordinateBound M ∧
    (2 * M + 8 * M^2) * Real.exp (6 * M) ≤ flowCoordinateBound M := by
  have h1 : 0 ≤ Real.exp (2 * M) := (Real.exp_pos _).le
  have h2 : 0 ≤ 2 * M := by positivity
  have h3 : 0 ≤ M * Real.exp (2 * M) := by positivity
  have h4 : 0 ≤ 2 * M * Real.exp (4 * M) := by positivity
  have h5 : 0 ≤ 4 * M + 2 * M^2 := by positivity
  have h6 : 0 ≤ (2 * M + M^2) * Real.exp (2 * M) := by positivity
  have h7 : 0 ≤ (M + 2 * M^2) * Real.exp (4 * M) := by positivity
  have h8 : 0 ≤ (2 * M + 8 * M^2) * Real.exp (6 * M) := by positivity
  dsimp [flowCoordinateBound]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem flowCoordinateBound_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ flowCoordinateBound M :=
  (by norm_num : (0 : ℝ) ≤ 3).trans (flowCoordinateBound_dominates hM).1

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {M : ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
variable (hM : 0 ≤ M)
variable (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
variable (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
variable (hq2 : ∀ i j : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j q) p| ≤ M)
variable (hq3 : ∀ i j k : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j (coordPartial k q)) p| ≤ M)
include hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3

end ActualFlow
end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

def spatialStrip (I : Set ℝ) : Set Coord := {p | p 0 ∈ I}

def separatedProduct (C f : ℝ → ℝ) (p : Coord) : ℝ := C (p 0) * f (p 1)

def taylorCorrection (C : ℝ → ℝ) (a : ℝ) (n : ℕ) : Coord → ℝ :=
  separatedProduct C (normalizedTimePower a (n + 2))

end SmoothLocal.Taylor

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def heightQCoefficient (g : MetricField) (z : Coord → ℝ) (i : Fin 6) (p : Coord) : ℝ :=
  qFirstCoefficient g i (qSolutionJet z p)

def qFirstJetPairRemainder (g : MetricField) (z : Coord → ℝ) (n : ℕ) (p : Coord) : ℝ :=
  coordPartial 0 (heightQCoefficient g z 2) p * coordPartial 0 (horizontalJet z n) p +
    coordPartial 0 (heightQCoefficient g z 3) p * coordPartial 1 (horizontalJet z n) p

def qCoordinateChainTerm (g : MetricField) (z : Coord → ℝ) (w : ChainWord) (p : Coord) : ℝ :=
  iteratedFDeriv ℝ w.arity (sixVariableQ g) (qSolutionJet z p)
    (fun i => horizontalJet (qSolutionJet z) (w.order i) p)

def qCoordinateChainSum (g : MetricField) (z : Coord → ℝ) (ws : List ChainWord) (p : Coord) : ℝ :=
  (ws.map (fun w => qCoordinateChainTerm g z w p)).sum

def actualQHighRemainder (g : MetricField) (z : Coord → ℝ) (m : ℕ) (p : Coord) : ℝ :=
  qCoordinateChainSum g z (topResidualWords m) p +
    (m + 3 : ℝ) * qFirstJetPairRemainder g z (m + 2) p

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

def heightStateFactor (z : Coord → ℝ) (n : ℕ) (j : Fin 4) : Coord → ℝ :=
  ![coordPartial 0 (verticalJet z n), coordPartial 1 (verticalJet z n),
    coordPartial 0 (coordPartial 1 (verticalJet z n)),
    coordPartial 1 (coordPartial 1 (verticalJet z n))] j

def heightStateBaseOrder : Fin 4 → ℕ := ![1, 1, 2, 2]

variable {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def directedFluxCostConstant (D M lambda S MI X : ℝ) : ℝ :=
  6*X*D*Real.exp (lambda*S+MI)*(M+1)

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

def chainProductL2Budget (B : ℝ) (H : ℝ≥0) (V : Set Coord) (ell : ℕ) : ℝ≥0∞ :=
  ‖B ^ ell‖ₑ * ((H : ℝ≥0∞) + (volume V) ^ (1 / (2 : ℝ)))

def chainWordL2Budget (C B : ℝ) (H : ℝ≥0) (V : Set Coord) (ell : ℕ)
    (w : ChainWord) : ℝ≥0∞ :=
  ∑ _r : Fin w.arity → Fin 6, ‖C‖ₑ * chainProductL2Budget B H V ell

def chainSumL2Budget (C B : ℝ) (H : ℝ≥0) (V : Set Coord) (ell : ℕ)
    (ws : List ChainWord) : ℝ≥0∞ :=
  (ws.map (chainWordL2Budget C B H V ell)).sum

def firstJetPairL2Budget (C : ℝ) (H : ℝ≥0) : ℝ≥0∞ :=
  ‖C‖ₑ * (H : ℝ≥0∞) + ‖C‖ₑ * (H : ℝ≥0∞)

def actualHighRemainderL2Budget (C Cfirst B : ℝ) (H : ℝ≥0) (V : Set Coord)
    (m : ℕ) : ℝ≥0∞ :=
  chainSumL2Budget C B H V (m + 3) (topResidualWords m) +
    ‖(m + 3 : ℝ)‖ₑ * firstJetPairL2Budget Cfirst H

variable {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

def capOuterLeft (L : ℝ) : ℝ := capOuterEdge (capOuterEdge L)
def capOuterLeftOne (L : ℝ) : ℝ := capInnerEdge (capOuterEdge L)
def capOuterRightOne (R : ℝ) : ℝ := -capInnerEdge (capOuterEdge (-R))
def capOuterRight (R : ℝ) : ℝ := -capOuterEdge (capOuterEdge (-R))
def capOuterBottom (A : ℝ) : ℝ := capOuterEdge (capOuterEdge A)
def capOuterBottomOne (A : ℝ) : ℝ := capInnerEdge (capOuterEdge A)

theorem capOuterRectangle_edges {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) :
    -2 < capOuterLeft L ∧ capOuterLeft L < capOuterLeftOne L ∧ capOuterLeftOne L < -3/2 ∧
    3/2 < capOuterRightOne R ∧ capOuterRightOne R < capOuterRight R ∧ capOuterRight R < 2 ∧
    -2 < capOuterBottom A ∧ capOuterBottom A < capOuterBottomOne A ∧
    capOuterBottomOne A < A ∧ capOuterLeft L < L ∧ R < capOuterRight R := by
  obtain ⟨hlo,hli,hlu,hlx⟩ := capEdges_bounds hL
  obtain ⟨hro,hri,hru,hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao,hai,hau,hax⟩ := capEdges_bounds hA
  obtain ⟨hloo,hlio,hluo,hlxo⟩ := capEdges_bounds hlo
  obtain ⟨hroo,hrio,hruo,hrxo⟩ := capEdges_bounds hro
  obtain ⟨haoo,haio,hauo,haxo⟩ := capEdges_bounds hao
  unfold capOuterLeft capOuterLeftOne capOuterRightOne capOuterRight capOuterBottom capOuterBottomOne
  refine ⟨hloo,hlio,hluo,?_,?_,?_,haoo,haio,?_,?_,?_⟩ <;> linarith

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

def qResidual (g : MetricField) (P : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 1 (coordPartial 1 P) p - sixVariableQ g (qSolutionJet P p)

def nextTaylorCoefficient (g : MetricField) (a : ℝ) (P : Coord → ℝ)
    (n : ℕ) (x : ℝ) : ℝ :=
  -verticalJet (qResidual g P) n ![x, a]

end SmoothLocal.Taylor

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def flowRhoJetBound (M : ℝ) : ℝ :=
  1 / Real.exp (-2 * M) + flowCoordinateBound M / (Real.exp (-2 * M))^2
def heightG1JetBound (G Z d c : ℝ) : ℝ :=
  4 * (darbouxGJetBound G Z d c * (1 + flowCoordinateBound (heightQuotientJetBound G Z d c))) *
    (flowRhoJetBound (heightQuotientJetBound G Z d c))^2
def heightBJetBound (G Z d c : ℝ) (ell : ℕ) : ℝ :=
  (heightPFirstBound G Z d c + 2 * (ell : ℝ) * heightQuotientJetBound G Z d c) *
    (1 + flowCoordinateBound (heightQuotientJetBound G Z d c))
def heightG1Lower (G Z d c e0 : ℝ) : ℝ :=
  e0 / (1 + hessianJetBound G Z d)^2 *
    (1 / Real.exp (2 * heightQuotientJetBound G Z d c))^2
def heightRemainderBound (G Z d c e0 : ℝ) (ell : ℕ) : ℝ :=
  (heightDriftErrorBound G Z d c + darbouxGJetBound G Z d c) /
      ((e0 / (1 + hessianJetBound G Z d)^2) * (1 / Real.exp (2 * heightQuotientJetBound G Z d c))) +
    (2 * (ell : ℝ) + 1) *
      (flowCoordinateBound (heightQuotientJetBound G Z d c) /
        (Real.exp (-2 * heightQuotientJetBound G Z d c))^3) /
      (1 / Real.exp (2 * heightQuotientJetBound G Z d c))^2

theorem heightG1Lower_pos {G Z d c e0 : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (he0 : 0 < e0) :
    0 < heightG1Lower G Z d c e0 := by
  have hH := hessianJetBound_nonneg hG hZ hd
  dsimp [heightG1Lower]
  positivity

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def capDistanceBound (A b : ℝ) : ℝ := b-capOuterBottom A

def capOverlapEnergyCost (L R A b kappa c1 c2 glow M lambda MI : ℝ) : ℝ :=
  let D := capDistanceBound A b
  let c := capOverlapThreshold kappa c1 D
  (directedFluxCostConstant D M lambda 2 MI (capSpatialDerivativeConstant L R A) +
    directedDefectCostConstant D M lambda 2 MI c2)*(D+1/(glow*c))

def capEllipticRatioBudget (L R A b kappa c1 glow MK M : ℝ) : ℝ :=
  let D := capDistanceBound A b
  let c := capOverlapThreshold kappa c1 D
  ellipticRatioConstant D (glow*c/2)
    (ellipticCutoffDerivativeConstant c MK
      (threeEdgeDerivativeConstant (capOuterLeft L) (capOuterLeftOne L) (capOuterRightOne R)
        (capOuterRight R) (capOuterBottom A) (capOuterBottomOne A))) M

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

def linearCauchy (a : ℝ) (u0 u1 : ℝ → ℝ) (p : Coord) : ℝ :=
  u0 (p 0) + u1 (p 0) * (p 1 - a)

def taylorApproximation (g : MetricField) (a : ℝ) (u0 u1 : ℝ → ℝ) : ℕ → Coord → ℝ
  | 0 => linearCauchy a u0 u1
  | n + 1 => fun p => taylorApproximation g a u0 u1 n p +
      taylorCorrection (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) a n p

end SmoothLocal.Taylor

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

structure QPulsePointBounds (gStar gTau : MetricField) (z : Coord → ℝ)
    (U : Set Coord) (q0 a delta tau : ℝ) (N : ℕ)
    (B Bcompare BQ D A d dcompare c epsilon epsilonQ : ℝ) (p : Coord) : Prop where
  point_mem : inverseShearCoordinates q0 p ∈ U
  referenceFirst : ‖actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤ B
  referenceDet : d ≤ (metricInShearCoordinates gStar q0 p).det
  testFirst : ‖actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
    (inverseShearCoordinates q0 p)‖ ≤ Bcompare
  testDet : dcompare ≤ (testMetric gStar q0 a N delta tau (inverseShearCoordinates q0 p)).det
  approximationFirst : ‖actualCurvatureFirstInput gTau (inverseShearCoordinates q0 p)-
    actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
      (inverseShearCoordinates q0 p)‖ ≤ epsilon
  approximationSecond : ∀ i j k l : Fin 2,
    |coordPartial i (coordPartial j (fun q => gTau q k l)) (inverseShearCoordinates q0 p)-
      coordPartial i (coordPartial j (fun q => testMetric gStar q0 a N delta tau q k l))
        (inverseShearCoordinates q0 p)| ≤ epsilon
  referenceState : ‖qFirstBundle (metricInShearCoordinates gStar q0)
    (qSolutionJet (heightInShearCoordinates z q0) p)‖ ≤ BQ
  referenceXX : c ≤ |covHessian (metricInShearCoordinates gStar q0)
    (heightInShearCoordinates z q0) p 0 0|
  baseFirstDistance : ‖actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p-
    actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤ epsilonQ
  actualDensity : |curvatureDensity gTau (inverseShearCoordinates q0 p)| ≤ D
  referenceCoefficient : |forcingCoefficient (metricInShearCoordinates gStar q0)
    (heightInShearCoordinates z q0) p| ≤ A

def actualShearedQForcing (gStar gTau : MetricField) (z : Coord → ℝ) (q0 : ℝ) (p : Coord) : ℝ :=
  sixVariableQ (metricInShearCoordinates gTau q0) (qSolutionJet (heightInShearCoordinates z q0) p)-
    sixVariableQ (metricInShearCoordinates gStar q0) (qSolutionJet (heightInShearCoordinates z q0) p)

def qForcingRemainderBudget (A Cfirst Ctest Ccompare a : ℝ) (ha : 0 < a)
    (N : ℕ) (delta tau epsilon epsilonQ : ℝ) : ℝ :=
  2*A*(testDensityErrorCoefficient Ctest a ha delta*tau/tau^N+Ccompare*epsilon)+Cfirst*epsilonQ

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow

end SmoothLocal.Geometry

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def heightAJetBound (G Z d c : ℝ) : ℝ :=
  2 * heightG1JetBound G Z d c *
    (curvatureFirstBound G d * (1 + flowCoordinateBound (heightQuotientJetBound G Z d c)))

theorem heightG1JetBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightG1JetBound G Z d c := by
  have hQ := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hQ
  have hDG := darbouxGJetBound_nonneg (Z := Z) (d := d) hG hc
  dsimp [heightG1JetBound]; positivity

theorem heightAJetBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightAJetBound G Z d c := by
  have hG1 := heightG1JetBound_nonneg hG hZ hd hc
  have hQ := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hQ
  have hK := curvatureFirstBound_nonneg hG hd
  dsimp [heightAJetBound]; positivity

theorem heightBJetBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (ell : ℕ) :
    0 ≤ heightBJetBound G Z d c ell := by
  have hQ := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hQ
  have hP := heightPFirstBound_nonneg hG hZ hd hc
  dsimp [heightBJetBound]; positivity

theorem heightRemainderBound_nonneg {G Z d c e0 : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0) (ell : ℕ) :
    0 ≤ heightRemainderBound G Z d c e0 ell := by
  have hQ := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hQ
  have hDE := heightDriftErrorBound_nonneg hG hZ hd hc
  have hDG := darbouxGJetBound_nonneg (Z := Z) (d := d) hG hc
  have hH := hessianJetBound_nonneg hG hZ hd
  dsimp [heightRemainderBound]; positivity

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry SmoothLocal.Flow

def capInteriorWeightFloor (top b lambda MI : ℝ) : ℝ :=
  (b-top)^8*Real.exp (-lambda*top-MI)

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.HighEquation

def BoundedAdmissibleHeight (g : MetricField) (M : ℕ) (z : Coord → ℝ) : Prop :=
  0 < M ∧ PatchAdmissibleHeight g z ∧
  (∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ (M : ℝ)) ∧
  (∀ p ∈ modelSquare, 1 / (M : ℝ) ≤ |covHessian g z p 1 1| ∧
    |covHessian g z p 1 1| ≤ (M : ℝ)) ∧
  (∀ p ∈ modelSquare, 1 / (M : ℝ) ≤ heightEnergy g z p)

end SmoothLocal.Geometry

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

def boundedClassSpeed (kappa : ℝ) (M : ℕ) : ℝ :=
  Real.sqrt (kappa / 2) * (M : ℝ) ^ (-(3 : ℝ) / 2)

def boundedClassWidth (kappa : ℝ) (M : ℕ) : ℝ :=
  100 * (1 + (boundedClassSpeed kappa M)⁻¹)

end SmoothLocal.Perturbation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

def mixedRemainderL2Budget (C B : ℝ) (H : ℝ≥0) (V : Set Coord) (k : ℕ) : ℝ≥0∞ :=
  firstJetPairL2Budget C H +
    ∑ c : OrderedFinpartition k, chainWordL2Budget C B H V k ⟨c.length, c.partSize⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def heightCapCurvatureBound (G Z d c : ℝ) : ℝ :=
  curvatureFirstBound G d*(1+flowCoordinateBound (heightQuotientJetBound G Z d c))

def heightCapCValueBound (G Z d c e0 : ℝ) (ell : ℕ) : ℝ :=
  ((ell : ℝ)+1)*heightAJetBound G Z d c +
    heightAJetBound G Z d c*heightRemainderBound G Z d c e0 ell

def heightCapCoefficientBound (G Z d c e0 : ℝ) (ell : ℕ) : ℝ :=
  heightAJetBound G Z d c + 2*heightBJetBound G Z d c ell + heightCapCValueBound G Z d c e0 ell

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

def mixedXBudget (C : ℝ) (R : ℝ≥0∞) (Htop : ℝ≥0) : ℕ → ℝ≥0∞
  | 0 => (Htop : ℝ≥0∞) + R
  | n + 1 => (1 + ‖C‖ₑ + ‖C‖ₑ) * mixedXBudget C R Htop n

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

def HeightNumericData (G Z d c e0 kappa : ℝ) : Prop :=
  0 ≤ G ∧ 0 ≤ Z ∧ 0 < d ∧ 0 < c ∧ 0 < e0 ∧ 0 < kappa

def HeightDirectedBudgets (G Z d c e0 kappa : ℝ) (ell : ℕ) (v : ℝ × ℝ × ℝ) : Prop :=
  let epsilon := v.1
  let lambda := v.2.1
  let c1 := v.2.2
  let rhoMax := 1/Real.exp (-2*heightQuotientJetBound G Z d c)
  let cG := heightG1Lower G Z d c e0
  let MG := heightG1JetBound G Z d c
  let MB := heightBJetBound G Z d c ell
  let Mr := heightRemainderBound G Z d c e0 ell
  let MA := heightAJetBound G Z d c
  0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧
  epsilon*2*((1 : ℝ)/100) ≤ ((ell : ℝ)+1/2)/rhoMax ∧
  2*(2*MB+epsilon+epsilon*2*MB) ≤ lambda ∧
  (2*MB+1+2*MB)/2+Mr ≤ lambda/8 ∧
  4*(2*((ell : ℝ)*MA+MA*Mr+MA*(2*MB)+1))^2*epsilon^2*MA ≤ 1/8 ∧
  (4*(2*((ell : ℝ)*MA+MA*Mr+MA*(2*MB)+1))^2*epsilon^2)/lambda ≤
    modelCoercivityMargin cG kappa rhoMax epsilon ell/8 ∧
  directedPrincipalBound ell epsilon 2 MA MA+modelCoercivityMargin cG kappa rhoMax epsilon ell/2 ≤
    lambda*(cG*modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell)/4 ∧
  c1*2 ≤ modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell ∧
  MG*c1*(lambda*2+8) ≤ modelCoercivityMargin cG kappa rhoMax epsilon ell/6

theorem exists_heightDirectedBudgets {G Z d c e0 kappa : ℝ}
    (h : HeightNumericData G Z d c e0 kappa) (ell : ℕ) :
    ∃ v : ℝ × ℝ × ℝ, HeightDirectedBudgets G Z d c e0 kappa ell v := by
  obtain ⟨hG,hZ,hd,hc,he0,hk⟩ := h
  have hcG := heightG1Lower_pos (c := c) hG hZ hd he0
  have hrho : 0 < 1/Real.exp (-2*heightQuotientJetBound G Z d c) := by positivity
  have hMG := heightG1JetBound_nonneg hG hZ hd hc
  have hMB := heightBJetBound_nonneg hG hZ hd hc ell
  have hMr := heightRemainderBound_nonneg hG hZ hd hc he0 ell
  have hMA := heightAJetBound_nonneg hG hZ hd hc
  obtain ⟨epsilon,lambda,c1,hbudget⟩ :=
    exists_directed_parameters ell hk hcG hrho hMG (show 0 ≤ 2*heightBJetBound G Z d c ell by positivity)
      hMB hMr hMA hMA hMA hMG (by norm_num : (0 : ℝ) ≤ 2)
  exact ⟨(epsilon,lambda,c1),hbudget⟩

def heightDirectedNumbers (G Z d c e0 kappa : ℝ) (ell : ℕ) : ℝ × ℝ × ℝ := by
  classical
  exact if h : HeightNumericData G Z d c e0 kappa then Classical.choose (exists_heightDirectedBudgets h ell)
    else (1,1,1)

def heightDirectedEpsilon (G Z d c e0 kappa : ℝ) (ell : ℕ) : ℝ :=
  (heightDirectedNumbers G Z d c e0 kappa ell).1
def heightDirectedLambda (G Z d c e0 kappa : ℝ) (ell : ℕ) : ℝ :=
  (heightDirectedNumbers G Z d c e0 kappa ell).2.1
def heightDirectedSlope (G Z d c e0 kappa : ℝ) (ell : ℕ) : ℝ :=
  (heightDirectedNumbers G Z d c e0 kappa ell).2.2
def heightDirectedCoercivity (G Z d c e0 kappa : ℝ) (ell : ℕ) : ℝ :=
  min (heightDirectedLambda G Z d c e0 kappa ell/8)
    (modelCoercivityMargin (heightG1Lower G Z d c e0) kappa
      (1/Real.exp (-2*heightQuotientJetBound G Z d c))
      (heightDirectedEpsilon G Z d c e0 kappa ell) ell/4)

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def HorizontalMetricTwoJetBound (g : MetricField) (p : Coord) (N : ℕ) (G : ℝ) : Prop :=
  (∀ i j n, n ≤ N → |horizontalJet (fun x => g x i j) n p| ≤ G) ∧
  (∀ d i j n, n ≤ N → |horizontalJet (coordPartial d (fun x => g x i j)) n p| ≤ G) ∧
  (∀ d e i j n, n ≤ N →
    |horizontalJet (coordPartial d (coordPartial e (fun x => g x i j))) n p| ≤ G)

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Analytic
open SmoothLocal.Geometry

end SmoothLocal.Analytic

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

def CoordinateL2Bound (z : Coord → ℝ) (V : Set Coord) (N : ℕ) (H : ℝ≥0) : Prop :=
  ∀ ds : List (Fin 2), ds.length ≤ N →
    eLpNorm' (iteratedCoordPartial ds z) (2 : ℝ) (volume.restrict V) ≤ (H : ℝ≥0∞)

end SmoothLocal.HighEquation

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Sobolev
open SmoothLocal.HighEquation

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Taylor

def actualComparisonSource (gStar gTau : MetricField) (z : Coord → ℝ)
    (q0 : ℝ) (P : Coord → ℝ) (p : Coord) : ℝ :=
  actualShearedQForcing gStar gTau z q0 p -
    qResidual (metricInShearCoordinates gStar q0) P p

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Analytic

def uniformMixedOrderBudget (C B : ℝ) (H Htop : ℝ≥0) (N : ℕ) : ℝ≥0 :=
  max H (mixedXBudget C (mixedRemainderL2Budget C B H modelSquare (N-2)) Htop N).toNNReal

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model SmoothLocal.HighEquation

def heightUniformCapEstimateRHS (G Z d c e0 kappa : ℝ) (ell : ℕ)
    (L R bottom top b : ℝ) (u f : Coord → ℝ) : ℝ :=
  let lambda := heightDirectedLambda G Z d c e0 kappa ell
  let c1 := heightDirectedSlope G Z d c e0 kappa ell
  let c2 := heightDirectedCoercivity G Z d c e0 kappa ell
  let M := heightCapCoefficientBound G Z d c e0 ell
  let MK := heightCapCurvatureBound G Z d c
  let glow := heightG1Lower G Z d c e0
  let MI := 2*heightBJetBound G Z d c ell
  let D := capDistanceBound bottom b
  let COverlap := capOverlapEnergyCost L R bottom b kappa c1 c2 glow M lambda MI
  let HElliptic := capEllipticRatioBudget L R bottom b kappa c1 glow MK M
  (2/(c2*capInteriorWeightFloor top b lambda MI))*
    ((((5/(2*c2))*(D^8*Real.exp (lambda*2+MI))+COverlap*D^6)*
      rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (f p)^2)) +
    ((COverlap*(D^6+HElliptic))*
      rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (u p)^2)))

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Topology NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

structure LowerCapRectangle (bStar : ℝ) where
  left : ℝ
  right : ℝ
  bottom : ℝ
  top : ℝ
  left_gt : -2 < left
  right_lt : right < 2
  bottom_gt : -2 < bottom
  horizontal : left ≤ right
  vertical : bottom ≤ top
  top_lt : top < bStar
  ceiling_le : bStar ≤ 0

namespace LowerCapRectangle

variable {bStar : ℝ}

def region (r : LowerCapRectangle bStar) : Set Coord := closedRectangle r.left r.right r.bottom r.top

def image (r : LowerCapRectangle bStar) (Y : ℝ → ℝ → ℝ) : Set Coord := capChart Y '' r.region

def energyOuter (r : LowerCapRectangle bStar) : LowerCapRectangle bStar where
  left := capOuterLeft r.left
  right := capOuterRight r.right
  bottom := capOuterBottom r.bottom
  top := (r.top+bStar) / 2
  left_gt := (capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt).1
  right_lt := (capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt).2.2.2.2.2.1
  bottom_gt := (capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt).2.2.2.2.2.2.1
  horizontal := by
    obtain ⟨_,_,_,_,_,_,_,_,_,hL,hR⟩ := capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt
    linarith [r.horizontal]
  vertical := by
    obtain ⟨_,_,_,_,_,_,_,hB0,hB1,_,_⟩ := capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt
    linarith [r.vertical,r.top_lt]
  top_lt := by linarith [r.top_lt]
  ceiling_le := r.ceiling_le

def margin (r : LowerCapRectangle bStar) : ℝ :=
  min ((r.left+2)/2) (min ((2-r.right)/2) (min ((r.bottom+2)/2) ((bStar-r.top)/2)))

theorem margin_pos (r : LowerCapRectangle bStar) : 0 < r.margin := by
  unfold margin
  apply lt_min
  · linarith [r.left_gt]
  · apply lt_min
    · linarith [r.right_lt]
    · apply lt_min <;> linarith [r.bottom_gt,r.top_lt]

theorem margin_bounds (r : LowerCapRectangle bStar) :
    r.margin ≤ (r.left+2)/2 ∧ r.margin ≤ (2-r.right)/2 ∧
    r.margin ≤ (r.bottom+2)/2 ∧ r.margin ≤ (bStar-r.top)/2 := by
  unfold margin
  refine ⟨min_le_left _ _, ?_, ?_, ?_⟩
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)

def expand (r : LowerCapRectangle bStar) : LowerCapRectangle bStar where
  left := r.left-r.margin
  right := r.right+r.margin
  bottom := r.bottom-r.margin
  top := r.top+r.margin
  left_gt := by linarith [r.margin_bounds.1,r.left_gt]
  right_lt := by linarith [r.margin_bounds.2.1,r.right_lt]
  bottom_gt := by linarith [r.margin_bounds.2.2.1,r.bottom_gt]
  horizontal := by linarith [r.horizontal,r.margin_pos]
  vertical := by linarith [r.vertical,r.margin_pos]
  top_lt := by linarith [r.margin_bounds.2.2.2,r.top_lt]
  ceiling_le := r.ceiling_le

end LowerCapRectangle

variable {bStar : ℝ}

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def heightCapIntegralFactors (G Z d c e0 kappa : ℝ) (ell : ℕ)
    (L R bottom top b : ℝ) : ℝ × ℝ :=
  let lambda := heightDirectedLambda G Z d c e0 kappa ell
  let c1 := heightDirectedSlope G Z d c e0 kappa ell
  let c2 := heightDirectedCoercivity G Z d c e0 kappa ell
  let M := heightCapCoefficientBound G Z d c e0 ell
  let MK := heightCapCurvatureBound G Z d c
  let glow := heightG1Lower G Z d c e0
  let MI := 2*heightBJetBound G Z d c ell
  let D := capDistanceBound bottom b
  let COverlap := capOverlapEnergyCost L R bottom b kappa c1 c2 glow M lambda MI
  let HElliptic := capEllipticRatioBudget L R bottom b kappa c1 glow MK M
  let S := 2/(c2*capInteriorWeightFloor top b lambda MI)
  (S*((5/(2*c2))*(D^8*Real.exp (lambda*2+MI))+COverlap*D^6),
    S*(COverlap*(D^6+HElliptic)))

def heightPhysicalCapConstant (G Z d c e0 kappa : ℝ) (ell : ℕ)
    (L R bottom top b : ℝ) : ℝ :=
  let H := Real.exp (2*heightQuotientJetBound G Z d c)
  let A := heightCapIntegralFactors G Z d c e0 kappa ell L R bottom top b
  H*(2+3*H^2)*H*(|A.1|+|A.2|+1)

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def QLowBounds (g : MetricField) (z : Coord → ℝ) (S : Set Coord)
    (s0 M speed : ℝ) : Prop :=
  ∀ p ∈ S, s0 ≤ heightQCoefficient g z 5 p ∧
    |heightQCoefficient g z 2 p| ≤ M ∧ |heightQCoefficient g z 3 p| ≤ M ∧
    |heightQCoefficient g z 5 p| ≤ M ∧
    |coordPartial 0 (heightQCoefficient g z 4) p| ≤ M ∧
    |coordPartial 0 (heightQCoefficient g z 5) p| ≤ M ∧
    |coordPartial 1 (heightQCoefficient g z 5) p| ≤ M ∧
    |heightQCoefficient g z 4 p| + Real.sqrt (heightQCoefficient g z 5 p) ≤ speed

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Weighted

def heightCauchyValue (z : Coord → ℝ) (a : ℝ) (x : ℝ) : ℝ := z ![x, a]

def heightCauchyVelocity (z : Coord → ℝ) (a : ℝ) (x : ℝ) : ℝ :=
  coordPartial 1 z ![x, a]

end SmoothLocal.Taylor

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Taylor
open SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def comparisonCoefficient (g : MetricField) (P z : Coord → ℝ) (i : Fin 6) (p : Coord) : ℝ :=
  averagedQCoefficient g (qSolutionJet P p) (qSolutionJet z p) i

def comparisonDifference (P z : Coord → ℝ) (p : Coord) : ℝ := z p-P p

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model
open SmoothLocal.HighEquation SmoothLocal.Analytic SmoothLocal.Sobolev

variable {bStar : ℝ}

structure CapInductionHeight (g : MetricField) (U : Set Coord) (Z c e0 : ℝ)
    (z : Coord → ℝ) : Prop where
  smooth : ContDiffOn ℝ ∞ z U
  lowJet : ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z
  denominator : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|
  energy : ∀ p ∈ modelSquare, e0 ≤ heightEnergy g z p
  quotient : ∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ)/100
  darboux : ∀ p ∈ modelSquare,
    (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p

def lowerCapConstant (G Z d c e0 kappa : ℝ) (ell : ℕ) (r : LowerCapRectangle bStar) : ℝ :=
  heightPhysicalCapConstant G Z d c e0 kappa ell r.left r.right r.bottom r.top ((r.top+bStar)/2)

structure CapInductionFlow (g : MetricField) (U : Set Coord) (G Z d c e0 kappa : ℝ)
    (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (W : Set Coord) : Prop where
  domainOpen : IsOpen W
  squareSubset : modelSquare ⊆ W
  domainSubset : W ⊆ U
  quotientSmooth : ContDiffOn ℝ ∞ (hessianQuotient g z) W
  quotientBound : CoordinateBound (hessianQuotient g z) modelSquare 3 (heightQuotientJetBound G Z d c)
  continuous : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2)
  jointSmooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2)
  start : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s
  ode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
    HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t
  range : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3
  displacement : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50
  physicalEstimate : ∀ m : ℕ, ∀ {bStar : ℝ}, ∀ r : LowerCapRectangle bStar,
    (∫ p in r.image Y, (coordPartial 0 (verticalJet z (m+3)) p)^2+(verticalJet z (m+4) p)^2) ≤
      lowerCapConstant G Z d c e0 kappa (m+3) r *
        ((∫ p in r.energyOuter.image Y, (actualHighRemainder g z m p)^2)+
          (∫ p in r.energyOuter.image Y, (verticalJet z (m+3) p)^2))

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model
open SmoothLocal.HighEquation SmoothLocal.Analytic SmoothLocal.Sobolev

abbrev CapMetricJetBudget (bStar : ℝ) := ℕ → LowerCapRectangle bStar → ℝ

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model
open SmoothLocal.HighEquation SmoothLocal.Analytic SmoothLocal.Sobolev

def lowerCapMetricRequests {bStar : ℝ} : ℕ → LowerCapRectangle bStar →
    List (ℕ × LowerCapRectangle bStar)
  | 0, _ => []
  | k+1, r => (k+8,r.energyOuter)::(k+7,r)::lowerCapMetricRequests k r.energyOuter.expand

def FiniteCapMetricJets {bStar : ℝ} (g : MetricField) (Y : ℝ → ℝ → ℝ)
    (J : CapMetricJetBudget bStar) (L : List (ℕ × LowerCapRectangle bStar)) : Prop :=
  ∀ b ∈ L, ∀ (i j : Fin 2) (n : ℕ), n ≤ b.1+2 →
    ∀ p ∈ b.2.image Y, ‖iteratedFDeriv ℝ n (fun q => g q i j) p‖ ≤ J b.1 b.2

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Taylor

def metricComparisonSource (g gRef : MetricField) (P z : Coord → ℝ) (p : Coord) : ℝ :=
  sixVariableQ g (qSolutionJet z p)-sixVariableQ gRef (qSolutionJet z p)-qResidual gRef P p

def comparisonEnergySpeed (C : ℝ) : ℝ := C+Real.sqrt C
def comparisonEnergyRate (C Z0 Z s0 : ℝ) : ℝ :=
  8*(C*(max 1 Z0+max 1 Z))*(1+1/s0)

end SmoothLocal.HighEquation

end

end OAI
end


