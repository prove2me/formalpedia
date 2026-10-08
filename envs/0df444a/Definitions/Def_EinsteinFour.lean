-- Prove2me | Definitions.Def_EinsteinFour
-- name    : EinsteinFour
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:09.528373+00:00
-- url     : https://prove2.me/theorems/d30440ca-8fb5-4264-bf6e-f54839f39090
-- statement:
--   For a smooth real four-dimensional manifold M, a smooth metric is a smooth positive-definite Riemannian metric on its tangent bundle. Its coordinate matrix is obtained by pulling the metric back along the inverse chart, using the four standard coordinate vectors. Coordinate derivatives and the inverse metric matrix determine Christoffel symbols, curvature components Rˡᵢⱼₖ, the Ricci components Ricᵢⱼ = ∑ₖ Rᵏₖᵢⱼ, and the sectional numerator g(R(u,v)v,u). The predicate IsEinstein requires one real constant λ such that Ric = λg at every point; HasPositiveSectionalCurvature requires this sectional numerator to be positive for every pair of linearly independent coordinate vectors at every point. The three comparison spaces are the unit sphere S⁴ in ℝ⁵, complex projective space ℂP², and real projective space ℝP⁴. Their prescribed distances are respectively arccos⟨p,q⟩ and, for either projective space, arccos(|⟨p,q⟩|/(‖p‖‖q‖)) using nonzero representatives. ScaledIsometricTo(g,a,d) means there is a bijection to the comparison space whose distances, viewed as extended nonnegative reals, equal √a times the Riemannian extended distance of g. An orthonormal frame at a point is a real 4 × 4 matrix E satisfying EᵀGE = I for the coordinate metric G; its associated linear map and vectors are matrix multiplication and its columns. The frame bundle consists of points equipped with such frames and receives the topology induced by their realizations as four tangent-bundle vectors. An orientation is a clopen subset of this bundle meeting every fiber, with membership of a second frame equivalent to its determinant having the same sign as a chosen member in that fiber. ClosedOrientedMetricFour packages a compact, connected, regular Hausdorff, second-countable smooth four-manifold with a smooth metric and such an orientation. Classified(g) is the proposition that some positive scale a identifies g with one of the three comparison distances. ClassificationOn(M) is the defined proposition that every Einstein metric with positive sectional curvature on a compact, connected, Hausdorff, second-countable smooth four-manifold M is Classified; this proposition itself does not assume an orientation and no classification theorem is asserted here.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EinsteinFour.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EinsteinFour.lean; bytes 16..6785
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

-- Lean 4.33 compatibility: exact bundled-manifold carrier and instances from
-- Mathlib/Geometry/Manifold/Category/MfldCat/OfModel.lean at
-- d13f23b723b8a846827a245b89c10fc7d3f11612 (Lean 4.34.1).
-- Copyright (c) 2026 Jack McCarthy. Apache 2.0; author: Jack McCarthy.
-- Category morphisms are not used by this challenge and are omitted.
section Lean433MfldCatCompatibility
open scoped Manifold ContDiff
universe u v

namespace ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]

/-- The category of `C^n` manifolds modeled on a fixed model with corners `I`. -/
structure MfldCat (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) where
  _mkInternal ::
  /-- The underlying type. -/
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  [chartedSpace : ChartedSpace H carrier]
  [isManifold : IsManifold I n carrier]

attribute [instance] MfldCat.topologicalSpace MfldCat.chartedSpace MfldCat.isManifold

initialize_simps_projections MfldCat (-topologicalSpace, -chartedSpace, -isManifold)

namespace MfldCat
variable {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} {M N P : MfldCat I n} {X Y Z : Type u}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I n Z]

instance : CoeSort (MfldCat I n) (Type u) := ⟨MfldCat.carrier⟩

attribute [coe] MfldCat.carrier

end MfldCat
end ModelWithCorners
end Lean433MfldCatCompatibility

namespace OAI

noncomputable section

open scoped Manifold ContDiff BigOperators ENNReal
open Bundle

namespace EinsteinFour

abbrev FourSpace := EuclideanSpace ℝ (Fin 4)
abbrev I4 := 𝓘(ℝ, FourSpace)

def coordinateVector (i : Fin 4) : FourSpace := EuclideanSpace.single i 1

abbrev RoundSphere4 := {x : EuclideanSpace ℝ (Fin 5) // ‖x‖ = 1}

abbrev ComplexProjective2 := Projectivization ℂ (EuclideanSpace ℂ (Fin 3))

abbrev RealProjective4 := Projectivization ℝ (EuclideanSpace ℝ (Fin 5))

def roundDistance (p q : RoundSphere4) : ℝ :=
  Real.arccos (inner ℝ p.val q.val)

def fubiniStudyDistance (p q : ComplexProjective2) : ℝ :=
  Real.arccos (‖inner ℂ p.rep q.rep‖ / (‖p.rep‖ * ‖q.rep‖))

def realProjectiveDistance (p q : RealProjective4) : ℝ :=
  Real.arccos (‖inner ℝ p.rep q.rep‖ / (‖p.rep‖ * ‖q.rep‖))

section Metric

variable (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

abbrev SmoothMetric :=
  ContMDiffRiemannianMetric I4 ∞ FourSpace (TangentSpace I4 : M → Type _)

variable {M}

def metricInChart (g : SmoothMetric M) (c : M) (z : FourSpace) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  let e := chartAt FourSpace c
  let d := mfderiv I4 I4 e.symm z
  fun i j => g.inner (e.symm z) (d (coordinateVector i)) (d (coordinateVector j))

def partialDeriv (f : FourSpace → ℝ) (i : Fin 4) (z : FourSpace) : ℝ :=
  fderiv ℝ f z (coordinateVector i)

def christoffel (g : SmoothMetric M) (c : M) (z : FourSpace)
    (k i j : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin 4, (metricInChart g c z)⁻¹ k l *
    (partialDeriv (fun w => metricInChart g c w j l) i z +
     partialDeriv (fun w => metricInChart g c w i l) j z -
     partialDeriv (fun w => metricInChart g c w i j) l z)

def curvatureComponent (g : SmoothMetric M) (c : M) (z : FourSpace)
    (l i j k : Fin 4) : ℝ :=
  partialDeriv (fun w => christoffel g c w l j k) i z -
  partialDeriv (fun w => christoffel g c w l i k) j z +
  ∑ p : Fin 4,
    (christoffel g c z l i p * christoffel g c z p j k -
     christoffel g c z l j p * christoffel g c z p i k)

def ricciInChart (g : SmoothMetric M) (c : M) (z : FourSpace)
    (i j : Fin 4) : ℝ :=
  ∑ k : Fin 4, curvatureComponent g c z k k i j

def sectionalNumerator (g : SmoothMetric M) (c : M) (z : FourSpace)
    (u v : FourSpace) : ℝ :=
  ∑ l : Fin 4, ∑ m : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4,
    metricInChart g c z l m * curvatureComponent g c z l i j k *
      u i * v j * v k * u m

def IsEinstein (g : SmoothMetric M) : Prop :=
  ∃ lam : ℝ, ∀ (c : M) (i j : Fin 4),
    ricciInChart g c (chartAt FourSpace c c) i j =
      lam * metricInChart g c (chartAt FourSpace c c) i j

def HasPositiveSectionalCurvature (g : SmoothMetric M) : Prop :=
  ∀ (c : M) (u v : FourSpace), LinearIndependent ℝ ![u, v] →
    0 < sectionalNumerator g c (chartAt FourSpace c c) u v

def scaledEDistance (g : SmoothMetric M) (a : ℝ) (x y : M) : ℝ≥0∞ :=
  letI : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  ENNReal.ofReal (Real.sqrt a) * Manifold.riemannianEDist I4 x y

def ScaledIsometricTo {N : Type*} (g : SmoothMetric M) (a : ℝ)
    (modelDistance : N → N → ℝ) : Prop :=
  ∃ f : M ≃ N, ∀ x y : M,
    ENNReal.ofReal (modelDistance (f x) (f y)) = scaledEDistance g a x y

end Metric

end EinsteinFour


namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

def chartMetric (g : SmoothMetric M) (c : M) : Mat4 :=
  metricInChart g c (chartAt FourSpace c c)

structure OrthonormalFrame (g : SmoothMetric M) (c : M) where
  matrix : Mat4
  orthonormal : matrixᵀ * chartMetric g c * matrix = 1

def OrthonormalFrame.map {g : SmoothMetric M} {c : M} (e : OrthonormalFrame g c) :
    FourSpace →ₗ[ℝ] FourSpace :=
  (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm.toLinearMap ∘ₗ
    (Matrix.mulVecLin e.matrix) ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).toLinearMap

def OrthonormalFrame.vector {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (i : Fin 4) : FourSpace :=
  WithLp.toLp 2 (fun a => e.matrix a i)

structure FrameBundle (g : SmoothMetric M) where
  base : M
  frame : OrthonormalFrame g base

def frameRealization {g : SmoothMetric M} (e : FrameBundle g) :
    M × (Fin 4 → TangentBundle I4 M) :=
  (e.base, fun i => ⟨e.base, e.frame.vector i⟩)


instance (g : SmoothMetric M) : TopologicalSpace (FrameBundle g) :=
  TopologicalSpace.induced frameRealization inferInstance

/-- An orientation is a clopen choice of determinant sign in every frame fiber. -/
structure FrameOrientation (g : SmoothMetric M) where
  positive : Set (FrameBundle g)
  clopen : IsClopen positive
  nonempty_fiber : ∀ c, ∃ e : OrthonormalFrame g c, (⟨c, e⟩ : FrameBundle g) ∈ positive
  compatible : ∀ c (e f : OrthonormalFrame g c),
    (⟨c, e⟩ : FrameBundle g) ∈ positive →
      ((⟨c, f⟩ : FrameBundle g) ∈ positive ↔ 0 < e.matrix.det * f.matrix.det)

end PositiveEinsteinFour.Geometry

namespace PositiveEinsteinFour

open EinsteinFour

universe u

/-- A connected closed oriented smooth Riemannian four-manifold. -/
structure ClosedOrientedMetricFour where
  manifold : ModelWithCorners.MfldCat.{u} I4 ∞
  [regular : T3Space manifold]
  [secondCountable : SecondCountableTopology manifold]
  [compact : CompactSpace manifold]
  [connected : ConnectedSpace manifold]
  metric : SmoothMetric manifold
  orientation : Geometry.FrameOrientation metric

attribute [instance] ClosedOrientedMetricFour.regular
  ClosedOrientedMetricFour.secondCountable ClosedOrientedMetricFour.compact
  ClosedOrientedMetricFour.connected

section ClassificationDefinitions

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Positive rescaling identifies the metric with one of the three standard models. -/
def Classified (g : SmoothMetric M) : Prop :=
  ∃ a : ℝ, 0 < a ∧
    (ScaledIsometricTo g a roundDistance ∨
      ScaledIsometricTo g a fubiniStudyDistance ∨
      ScaledIsometricTo g a realProjectiveDistance)

def ClassificationOn (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ConnectedSpace M] : Prop :=
  ∀ g : SmoothMetric M,
    IsEinstein g → HasPositiveSectionalCurvature g → Classified g

end ClassificationDefinitions



end PositiveEinsteinFour
end
end OAI


