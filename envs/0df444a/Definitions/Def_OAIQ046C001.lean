-- Prove2me | Definitions.Def_OAIQ046C001
-- name    : OAIQ046C001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:41:35.335302+00:00
-- url     : https://prove2.me/theorems/eb20c0ea-5cd4-416e-82e1-a76fda7b00e7
-- title:
--   Definitions bundle OAIQ046C001 of the split of OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CannonRelease.cannon`, carved from OpenAI's openai/math development (OpenAI, *A Modulus Proof of Cannon's Conjecture (result family 246)*, OpenAI Math Release, September 23, 2026, result family 246, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 147 declarations of OpenAI's Lean: 109 definitions, 5 instances and 33 theorems. The definitions and types are `OAI.CannonMagnification.denominator`, `OAI.CannonMagnification.normalized`, `OAI.CannonMagnification.onDomain`, `OAI.CannonMetricQC.DensityOne`, `OAI.CannonMetricQC.PointwiseLip`, `OAI.CannonMetricQC.WeakQS`, `OAI.CannonMetricQC.cutoffBump`, `OAI.CannonMetricQC.derivativeDet`, `OAI.CannonMetricQC.derivativeMatrix`, `OAI.CannonMetricQC.imageArea`, `OAI.CannonMetricQC.lipPiece`, `OAI.CannonMetricQC.mollifier`, `OAI.CannonMetricQC.mollify`, `OAI.CannonMetricQC.smoothCutoff`, `OAI.CannonMobius.Mat`, `OAI.CannonMobius.Round`, `OAI.CannonMobius.north`, `OAI.CannonMobius.planeHyperplane`, `OAI.CannonNode.childLower`, `OAI.CannonNode.childUpper`, `OAI.CannonNode.fraction`, `OAI.CannonOrientation.HasIncrement`, `OAI.CannonOrientation.circle`, `OAI.CannonOrientation.clip`, `OAI.CannonPacking.PolynomialPacking`, `OAI.CannonPackingGeometry.RingData`, `OAI.CannonPackingGeometry.SectorRingData`, `OAI.CannonPackingGeometry.angleEntropy`, `OAI.CannonPackingGeometry.angleFeasible`, `OAI.CannonPackingGeometry.angleMove`, `OAI.CannonPackingGeometry.angleSum`, `OAI.CannonPackingGeometry.cornerAngle`, `OAI.CannonPackingGeometry.cornerConstraint`, `OAI.CannonPackingGeometry.faceCornerSum`, `OAI.CannonPackingGeometry.fanRay`, `OAI.CannonPackingGeometry.fanSucc`, `OAI.CannonPackingGeometry.neighborFaces`, `OAI.CannonPackingGeometry.petalAngle`, `OAI.CannonPackingGeometry.vertexCornerSum`, `OAI.CannonPaths.SphereTwo` and 69 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/Cannon, in whole or in part: `Cannon_Actions_Triples`, `Cannon_Beltrami_Increment`, `Cannon_Beltrami_RectCrossing`, `Cannon_Boundary_BoundaryHomeomorph`, `Cannon_Boundary_PolynomialPacking`, `Cannon_Boundary_Thin`, `Cannon_Boundary_VisualScale`, `Cannon_Boundary_VisualSynchronousPrefix`, `Cannon_CirclePacking_AngleGradient`, `Cannon_CirclePacking_Cycle`, `Cannon_CirclePacking_Demand`, `Cannon_CirclePacking_Det`, `Cannon_CirclePacking_OrientedArea`, `Cannon_CirclePacking_PetalAngle`, `Cannon_CirclePacking_SectorRingData`, `Cannon_CirclePacking_TrianglePoint`, `Cannon_Conformal_BoundedCrossRatios`, `Cannon_Conformal_CutoffBump`, `Cannon_Conformal_Distinct`, `Cannon_Conformal_FiniteB`, `Cannon_Conformal_ImageArea`, `Cannon_Conformal_PreservesProducts`, `Cannon_Conformal_Round`, `Cannon_Conformal_Sphere`, `Cannon_Conformal_SphereMeasure`, `Cannon_Conformal_SphereTwo`, `Cannon_Energy_Square`, `Cannon_Flows_Domain`, `Cannon_Flows_Lower`, `Cannon_Flows_State`, `Cannon_Flows_WeightedOscillation`, `Cannon_PlanarGraphs_PositiveHalfAxis`, `Cannon_PlaneTopology_ClosedInside`, `Cannon_PlaneTopology_Crossing`, `Cannon_PlaneTopology_FiniteSupport`, `Cannon_PlaneTopology_Lift`, `Cannon_PlaneTopology_Plane`, `Cannon_PlaneTopology_RadialStable`, `Cannon_PlaneTopology_Reverse`, `Cannon_PlaneTopology_SquareSide`, `Cannon_ScalarLimits_Osc`, `Cannon_ScalarLimits_Words`, `Cannon_Topology_CenteredHomeomorph`, `Cannon_Topology_Plane`, `Cannon_Topology_PlaneBox`, `Cannon_Uniformization_AnnulusFamily`, `Cannon_Uniformization_EventualRelativeShrink`, `Cannon_Uniformization_LayerFamily`.
--
--   **Imports.** It imports the published bundle `Def_CannonGeometricAction`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ046C002`; the statements `OAI.CannonConformal.measurable_structure_integration`, `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.disk_disjoint_of_interior`, `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.hull_geometry` and `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.univalent_triangles`; the proofs of `OAI.CannonBeltrami.normalized_smooth_beltrami_solution`, `OAI.CannonConformal.measurable_structure_integration`, `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.circle_packing`, `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.hull_geometry`, `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.univalent_triangles`, `OAI.CannonEmbeddedArc.Arc.exists_global_radius_constant`, `OAI.CannonEmbeddedArc.Arc.face_incidence_card_le`, `OAI.CannonEmbeddedArc.Arc.facialCycle_exists` and `OAI.CannonEmbeddedArc.Arc.triangular_disk_gauge_integrates`.
-- source:
--   OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 246; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Modulus-Proof-of-Cannons-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/Cannon at commit adc7f12

import Mathlib
import Definitions.Def_CannonGeometricAction

section
-- module Solutions.OAIQ046_CN.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Sphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonSphereReflection
open Set Metric Topology
open scoped OnePoint

abbrev S := OnePoint ℂ

end CannonSphereReflection

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_TrianglePoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonPackingGeometry
open Set

def cornerAngle {V A : Type*} (vertex : A × Fin 3 → V) (θ : A × Fin 3 → ℝ)
    (f : A) (v : V) : ℝ := by
  classical
  exact ∑ k : Fin 3, if vertex (f,k)=v then θ (f,k) else 0

end CannonPackingGeometry

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_Demand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleCuts
open Finset

variable {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]

def demand (out : Finset V) (v : V) : ℕ := if v∈out then 1 else 6
end CannonTriangleCuts

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_AngleGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variational angle functional for a conformal circle packing. -/

section
section
section
section
namespace CannonPackingGeometry
open Set Filter Topology MeasureTheory

noncomputable section

def angleEntropy (θ : ℝ) : ℝ :=
  2 * ((∫ x in (0:ℝ)..θ/2, Real.log (Real.sin x)) -
    (∫ x in (0:ℝ)..θ/2, Real.log (Real.cos x)))

end
end CannonPackingGeometry

namespace CannonPackingGeometry
open Set Filter Topology

noncomputable section

variable {I : Type*} [Fintype I]

def angleMove (x s t : ℝ) : ℝ := x+t*(s-x)

end
end CannonPackingGeometry

namespace CannonPackingGeometry
open Set Filter Topology

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

def angleSum (x : I → ℝ) : ℝ := ∑ i, angleEntropy (x i)

def angleFeasible (L : J → (I → ℝ) →L[ℝ] ℝ) (b : J → ℝ) : Set (I → ℝ) :=
  {x | (∀ i, x i ∈ Icc (0:ℝ) Real.pi) ∧ ∀ j, L j x=b j}

end
end CannonPackingGeometry

namespace CannonPackingGeometry
open Set

noncomputable section
variable {F V : Type*} [Fintype F] [Fintype V] [DecidableEq F] [DecidableEq V]

def faceCornerSum (f : F) : ((F × Fin 3) → ℝ) →L[ℝ] ℝ :=
  ∑ k : Fin 3, ContinuousLinearMap.proj (f,k)

def vertexCornerSum (vertex : F × Fin 3 → V) (v : V) : ((F × Fin 3) → ℝ) →L[ℝ] ℝ :=
  ∑ i : F × Fin 3, if vertex i=v then ContinuousLinearMap.proj i else 0

def cornerConstraint (vertex : F × Fin 3 → V) :
    (F ⊕ V) → ((F × Fin 3) → ℝ) →L[ℝ] ℝ :=
  Sum.elim faceCornerSum (vertexCornerSum vertex)

end
end CannonPackingGeometry

end
section
noncomputable section
namespace CannonPackingGeometry
open Finset Function

variable {V F : Type*} [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]

def neighborFaces (R : V → F → Prop) [DecidableRel R] (S : Finset V) : Finset F :=
  univ.filter (fun f => ∃ v∈S, R v f)

end CannonPackingGeometry

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Plane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
noncomputable section
namespace CannonRegularDisk
open Metric
open Set Metric Topology

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev RoundSphere := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

section Topological
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def IsRegularDisk (U : Set X) : Prop :=
  ∃ (e : Plane → X), IsOpenEmbedding e ∧ ∃ (q : Plane) (r : ℝ),
    0 < r ∧ U=e '' ball q r

end Topological

end CannonRegularDisk

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_FiniteSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

namespace CannonPolygonal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def FiniteSupport (S : Set E) : Prop :=
  ∃ P : Finset (E×E), S⊆⋃ p∈P, segment ℝ p.1 p.2

def PolyJoined (U : Set E) : E → E → Prop :=
  Relation.ReflTransGen (fun x y => segment ℝ x y⊆U)

end CannonPolygonal

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Lift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

namespace CannonWinding

def lift (f : C(I,Circle)) : C(I,ℝ) :=
  Circle.isCoveringMap_exp.liftPath f (Complex.arg (f 0)) (Circle.exp_arg (f 0)).symm

def turn (f : C(I,Circle)) : ℝ := lift f 1-lift f 0

end CannonWinding

namespace CannonWinding
variable {A : Type*} [TopologicalSpace A]

def direction (f : C(A,ℂ)) (hf : ∀ x, f x≠0) : C(A,Circle) := by
  let v (x : A) : Circle := ⟨f x/(‖f x‖:ℂ),by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr (hf x))]⟩
  refine ⟨v,?_⟩
  apply Continuous.subtype_mk
  exact f.continuous.div (Complex.continuous_ofReal.comp f.continuous.norm)
    (fun x => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hf x)))

@[simp] lemma direction_coe (f : C(A,ℂ)) (hf : ∀ x, f x≠0) (x : A) :
    (direction f hf x:ℂ)=f x/(‖f x‖:ℂ) := rfl

def winding (f : C(I,ℂ)) (z : ℂ) (hz : z∉range f) : ℝ :=
  turn (direction (f-.const I z) (fun t ht => hz ⟨t,sub_eq_zero.mp ht⟩))

end CannonWinding

namespace CannonWinding
open Metric

def roundLoop (a : ℂ) (R : ℝ) : C(I,ℂ) :=
  ⟨fun t => a+(R:ℂ)*(Circle.exp (2*Real.pi*(t:ℝ)):ℂ),by fun_prop⟩

lemma roundLoop_dist (a : ℂ) {R : ℝ} (hR : 0≤R) (t : I) : dist (roundLoop a R t) a=R := by
  simp only [dist_eq_norm,roundLoop,ContinuousMap.coe_mk,add_sub_cancel_left,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR,Circle.norm_coe,mul_one]

lemma center_not_roundLoop (a : ℂ) {R : ℝ} (hR : 0<R) : a∉range (roundLoop a R) := by
  rintro ⟨t,ht⟩
  have h := roundLoop_dist a hR.le t
  rw [ht,dist_self] at h
  exact hR.ne' h.symm

end CannonWinding

namespace CannonWinding
open Metric

def index (f : C(I,ℂ)) (z : ℂ) : ℝ := by
  classical
  exact if hz : z∉range f then winding f z hz else 0

end CannonWinding

namespace CannonWinding
open Metric

variable {X : Type*} [TopologicalSpace X] [T2Space X]

def chartIndex (e : ℂ → X) (he : IsOpenEmbedding e) (f : C(I,ℂ)) (x : X) : ℝ := by
  classical
  exact if x∈range e then index f ((he.toOpenPartialHomeomorph e).symm x) else 0

end CannonWinding

namespace CannonWinding
open Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X]

def complexPlane : ℂ ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  Complex.equivRealProdCLM.toHomeomorph.trans
    (Homeomorph.finTwoArrow.symm.trans (EuclideanSpace.equiv (𝕜:=ℝ) (ι:=Fin 2)).toHomeomorph.symm)

end CannonWinding

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonWinding
open Set Topology unitInterval

def blendPaths {a b : ℂ} (p q : Path a b) : p.Homotopy q where
  toFun st := (1-(st.1:ℝ)) • p st.2+(st.1:ℝ) • q st.2
  continuous_toFun := by fun_prop
  map_zero_left := by intro t; simp
  map_one_left := by intro t; simp
  prop' := by
    intro s t ht
    rcases ht with rfl|ht
    · simp
      ring
    · have : t=1 := ht
      subst t
      simp
      ring

def upperSemi : Path (-1 : ℂ) 1 where
  toFun t := Circle.exp (Real.pi*(1-(t:ℝ)))
  continuous_toFun := by fun_prop
  source' := by change (Circle.exp (Real.pi*(1-(0:ℝ))):ℂ)= -1; simp [Circle.coe_exp]
  target' := by simp

def lowerSemi : Path (-1 : ℂ) 1 where
  toFun t := Circle.exp (Real.pi*(1+(t:ℝ)))
  continuous_toFun := by fun_prop
  source' := by change (Circle.exp (Real.pi*(1+(0:ℝ))):ℂ)= -1; simp [Circle.coe_exp]
  target' := by
    change (Circle.exp (Real.pi*(1+(1:ℝ))):ℂ)=1
    rw [show Real.pi*(1+(1:ℝ))=2*Real.pi by ring,Circle.exp_two_pi]
    rfl

lemma upperSemi_norm (t : I) : ‖upperSemi t‖=1 := Circle.norm_coe _
lemma lowerSemi_norm (t : I) : ‖lowerSemi t‖=1 := Circle.norm_coe _
end CannonWinding

namespace CannonWinding
open Set Topology unitInterval Metric

lemma path_outside_avoids {a b : ℂ} (p : Path a b) (hp : ∀ t, 1≤‖p t‖)
    {z : ℂ} (hz : ‖z‖<1) : z∉range p := by
  rintro ⟨t,rfl⟩
  exact (hp t).not_gt hz

end CannonWinding

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_PositiveHalfAxis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonPlanarCorner
open Set Topology Metric

def positiveHalfAxis : Set (ℝ × ℝ) := {p | 0≤p.1 ∧ p.2=0}

end CannonPlanarCorner

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_RadialStable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonSegmentCones
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def RadialStable (K : Set E) (x : E) (ε : ℝ) : Prop :=
  ∀ y, dist y x < ε → ∀ t : ℝ, 0 < t → t ≤ 1 →
    (x + t • (y-x) ∈ K ↔ y ∈ K)

end CannonSegmentCones

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_OrientedArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonPackingGeometry
open Set ComplexConjugate

def fanRay (L α:ℕ→ℝ) (k:ℕ) : ℂ := (L k:ℂ)*(Circle.exp (∑ j∈Finset.range k,α j):ℂ)

@[simp] lemma fanRay_zero (L α:ℕ→ℝ) : fanRay L α 0=(L 0:ℂ) := by
  simp [fanRay]

def fanSucc {n:ℕ} (hn:0<n) (i:Fin n) : Fin n :=
  if h:i.val+1<n then ⟨i.val+1,h⟩ else ⟨0,hn⟩

end CannonPackingGeometry

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleWinding
open Set

attribute [local instance] Classical.propDecidable

def crossing (y z A : ℝ) : ℤ :=
  if y<0 ∧ 0<z ∧ 0<A then 1 else if z<0 ∧ 0<y ∧ A<0 then -1 else 0

def area (a b c : ℂ) : ℝ :=
  (b.re-a.re)*(c.im-a.im)-(b.im-a.im)*(c.re-a.re)

def edgeIndex (p a b : ℂ) : ℤ := crossing (a.im-p.im) (b.im-p.im) (area a b p)

def Inside (a b c p : ℂ) : Prop := 0<area a b p ∧ 0<area b c p ∧ 0<area c a p

def Generic (a b c p : ℂ) : Prop :=
  a.im≠p.im ∧ b.im≠p.im ∧ c.im≠p.im ∧ area a b p≠0 ∧ area b c p≠0 ∧ area c a p≠0

end CannonTriangleWinding

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_Det
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonTangentWedges
open Set

def det (a b c : ℂ) : ℝ := (b.re-a.re)*(c.im-a.im)-(b.im-a.im)*(c.re-a.re)

end CannonTangentWedges

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_Cycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleBoundary
open Finset

def cycle {V R : Type*} [Add R] (f : V → V → R) (a b c : V) := f a b+f b c+f c a

def signed {R : Type*} [Neg R] (b : Bool) (x : R) := if b then x else -x

end CannonTriangleBoundary

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_ClosedInside
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleWinding
open Set Metric Topology

def ClosedInside (a b c p : ℂ) : Prop := 0≤area a b p ∧ 0≤area b c p ∧ 0≤area c a p

end CannonTriangleWinding

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_Thin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Thin geodesic triangles and fellow travelling in the Cayley graph. -/

section
section
section
section
section
section
noncomputable section

noncomputable section
open Set Topology

noncomputable section

namespace CannonRelease
open Set Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G)

def CayleyData.leftIso (g : G) : D.graph ≃g D.graph where
  toEquiv := Equiv.mulLeft g
  map_rel_iff' := SimpleGraph.mulCayley_adj_mul_iff_right

def Asymptotic (r s : ℕ → G) : Prop := ∃ C : ℕ, ∀ n, D.graph.dist (r n) (s n) ≤ C

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma Asymptotic.symm {r s : ℕ → G} (h : Asymptotic D r s) : Asymptotic D s r := by
  obtain ⟨C,hC⟩ := h
  exact ⟨C, fun n => by rw [SimpleGraph.dist_comm]; exact hC n⟩

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma Asymptotic.trans {r s t : ℕ → G} (h : Asymptotic D r s)
    (h' : Asymptotic D s t) : Asymptotic D r t := by
  obtain ⟨C,hC⟩ := h
  obtain ⟨E,hE⟩ := h'
  exact ⟨C+E, fun n => (@SimpleGraph.Connected.dist_triangle _ D.graph (r n) (s n) (t n) D.connected).trans
    (Nat.add_le_add (hC n) (hE n))⟩

end CannonRelease

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_BoundaryHomeomorph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
noncomputable section
noncomputable section
open Set Topology

noncomputable section
namespace CannonRelease
open Set Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) (hthin : D.ThinTriangles)
local instance instSetoidBasedRay_1 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonVisual
open SimpleGraph Filter Topology
open scoped Topology NNReal

variable {V : Type*} {G : SimpleGraph V} {o : V}

abbrev Ray (G : SimpleGraph V) (o : V) :=
  {r : ℕ → V // r 0 = o ∧ ∀ i j, G.dist (r i) (r j) = Nat.dist i j}

end CannonVisual

namespace CannonVisual
open SimpleGraph Filter Topology
open scoped Topology NNReal

variable {V : Type*} {G : SimpleGraph V} {o : V}

lemma exp_neg_mul_min {ε : ℝ} (hε : 0 ≤ ε) (a b : ℝ) :
    Real.exp (-ε * min a b) = max (Real.exp (-ε*a)) (Real.exp (-ε*b)) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left h (neg_nonpos.mpr hε))
  · rw [min_eq_right h, max_eq_right]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left h (neg_nonpos.mpr hε))

noncomputable def visualExponent (δ : ℕ) : ℝ := Real.log 2 / (2*(8*δ+6) : ℕ)

lemma visualExponent_pos (δ : ℕ) : 0 < visualExponent δ := by
  unfold visualExponent
  apply div_pos (Real.log_pos (by norm_num))
  positivity

lemma visualExponent_small (δ : ℕ) : Real.exp (visualExponent δ * (2*(8*δ+6) : ℕ)) ≤ 2 := by
  have h : ((2*(8*δ+6) : ℕ) : ℝ) ≠ 0 := by positivity
  rw [visualExponent, div_mul_cancel₀ _ h, Real.exp_log (by norm_num : (0:ℝ)<2)]

end CannonVisual

namespace CannonVisual
open SimpleGraph Filter Topology
open scoped Topology NNReal

variable {V : Type*} {G : SimpleGraph V} {o : V}

lemma tendsto_exp_linear {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => Real.exp (-(2*ε)*(n:ℝ))) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  simpa only [Function.comp_def, neg_mul] using tendsto_neg_atTop_atBot.comp
    (Filter.Tendsto.const_mul_atTop (by positivity : 0 < 2*ε)
      (tendsto_natCast_atTop_atTop (R := ℝ)))

end CannonVisual

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_VisualScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
noncomputable section
noncomputable section
open Set Topology

noncomputable section

namespace CannonVisual
noncomputable def visualScale (δ k : ℕ) : ℝ := Real.exp (-visualExponent δ * (2*k:ℕ))
end CannonVisual

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_SphereTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
noncomputable section
noncomputable section
open Set Topology

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonPaths
abbrev SphereTwo := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

end CannonPaths

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Actions_Triples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
namespace CannonTriples

open Set Metric

abbrev Triples (X : Type*) := {t : Fin 3 → X // Function.Injective t}

instance instTopologicalSpaceTriples {X : Type*} [TopologicalSpace X] : TopologicalSpace (Triples X) :=
  inferInstanceAs (TopologicalSpace {t : Fin 3 → X // Function.Injective t})

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def separation (t : Fin 3 → X) : ℝ := min (dist (t 0) (t 1)) (min (dist (t 0) (t 2)) (dist (t 1) (t 2)))

def map (f : X ≃ₜ Y) (t : Triples X) : Triples Y :=
  ⟨f ∘ t.val,f.injective.comp t.property⟩

end CannonTriples

end

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_PolynomialPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
noncomputable section
open Set Metric

namespace CannonPacking

variable {X : Type*} [MetricSpace X]

def PolynomialPacking (Q : ℕ) (C : ℝ) : Prop :=
  ∀ (x : X) (r s : ℝ), 0 < s → s ≤ r → r ≤ 1 →
    ∀ t : Finset X, (∀ y ∈ t, dist x y ≤ r) →
      (∀ y ∈ t, ∀ z ∈ t, y ≠ z → s ≤ dist y z) →
      (t.card : ℝ) ≤ C*(r/s)^Q

end CannonPacking

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_SquareSide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
namespace CannonRegularDisk
open Metric
open unitInterval

variable {X : Type*} [TopologicalSpace X]

def squareSide : Fin 4 → Set (I×I) :=
  ![{z | z.1=0},{z | z.1=1},{z | z.2=0},{z | z.2=1}]

def squareBoundary : Set (I×I) := ⋃ i, squareSide i

lemma mem_squareBoundary (z : I×I) :
    z∈squareBoundary ↔ z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 := by
  simp [squareBoundary,squareSide,Fin.exists_fin_succ]

end CannonRegularDisk

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Topology_Plane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

namespace CannonPlaneLinear
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def complexPlaneL : ℂ ≃L[ℝ] Plane :=
  Complex.equivRealProdCLM.trans
    ((LinearEquiv.finTwoArrow ℝ ℝ).symm.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (𝕜:=ℝ) (ι:=Fin 2)).symm)

end CannonPlaneLinear

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_PetalAngle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
namespace CannonPackingGeometry
open Set Metric

noncomputable section

def petalAngle (s t : ℝ) : ℝ := 2 * Real.arcsin (Real.sqrt (s*t))

@[simp] lemma petalAngle_zero_left (t : ℝ) : petalAngle 0 t = 0 := by
  simp [petalAngle]
@[simp] lemma petalAngle_zero_right (t : ℝ) : petalAngle t 0 = 0 := by
  simp [petalAngle]

def RingData (n : ℕ) (t α : ℕ → ℝ) : Prop :=
  (∀ i, t i ∈ Icc (0:ℝ) 1) ∧
  (∀ i, α i ∈ Icc (0:ℝ) (2*Real.pi)) ∧
  α 0 = 0 ∧ α n = 2*Real.pi ∧ t n = t 0 ∧
  (∀ i, i < n → α (i+1) = α i + petalAngle (t i) (t (i+1))) ∧
  (∀ i, i < n → ∀ j, j < n → i ≠ j →
    Real.cos (α i - α j) ≤ 1-2*t i*t j)

end
end CannonPackingGeometry

end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_SectorRingData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonPackingGeometry
open Set

def SectorRingData (n : ℕ) (t α : ℕ → ℝ) : Prop :=
  (∀ i,t i∈Icc (0:ℝ) 1) ∧ (∀ i,α i∈Icc (0:ℝ) Real.pi) ∧
  t 0=1/2 ∧ t n=1/2 ∧ α 0=0 ∧ α n=Real.pi/3 ∧
  (∀ i,i<n → α (i+1)=α i+petalAngle (t i) (t (i+1))) ∧
  ∀ i,i≤n → ∀ j,j≤n → i≠j → Real.cos (α i-α j)≤1-2*t i*t j

end CannonPackingGeometry

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Round
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

abbrev Round := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def north : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1
lemma north_norm : ‖north‖=1 := by simp [north]
lemma north_ne_zero : north ≠ 0 := by intro h; simpa [h] using north_norm

def planeHyperplane : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ north)ᗮ := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))=2+1) := ⟨by simp⟩
  exact Complex.isometryOfOrthonormal
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 north_ne_zero)

end CannonMobius

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Uniformization_AnnulusFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonUniformization
open Set Metric unitInterval

variable {X : Type*} [MetricSpace X]

def annulusFamily (o : X) (r R : ℝ) : Set (Set X) :=
  {A | ∃ u v : X, ∃ p : Path u v, A = range p ∧ dist u o ≤ r ∧ R ≤ dist v o}
end CannonUniformization

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_Square
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonRegularization

variable {X : Type*} [TopologicalSpace X]

def pathPrefix {x y : X} (p : Path x y) (t : I) : Path x (p t) where
  toFun s := p (min s t)
  continuous_toFun := p.continuous.comp (continuous_id.min continuous_const)
  source' := by rw [min_eq_left (show (0 : I) ≤ t from t.property.1)]; exact p.source
  target' := by rw [min_eq_right (show t ≤ (1 : I) from t.property.2)]

def suffix {x y : X} (p : Path x y) (t : I) : Path (p t) y where
  toFun s := p (max s t)
  continuous_toFun := p.continuous.comp (continuous_id.max continuous_const)
  source' := by rw [max_eq_right (show (0 : I) ≤ t from t.property.1)]
  target' := by rw [max_eq_left (show t ≤ (1 : I) from t.property.2)]; exact p.target

end CannonRegularization

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_Lower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
section
section
section
open Set Metric

namespace CannonNode

variable {X : Type*} [MetricSpace X] [ProperSpace X]

def childLower (a l : ℝ) : ℝ := max a l

def childUpper (b u : ℝ) : ℝ := min b u

def fraction (a b l u : ℝ) : ℝ := max 0 (childUpper b u-childLower a l)/(b-a)

lemma fraction_pos_iff {a b l u : ℝ} (hab : a < b) :
    0 < fraction a b l u ↔ childLower a l < childUpper b u := by
  rw [fraction,div_pos_iff_of_pos_right (sub_pos.mpr hab),lt_max_iff]
  simp only [lt_self_iff_false,false_or,sub_pos]

end CannonNode

end

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_State
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section

section

section

section

namespace CannonMagnification

open Set Metric

def denominator {X : Type*} [MetricSpace X] (x : X) (R : ℝ) (y : X) : ℝ :=
  max R (dist x y)

end CannonMagnification

end

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_Osc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open scoped NNReal ENNReal
open Set Filter Metric Topology
open Set Filter Topology

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace CannonScalarLimit

def osc {X : Type*} (K : Set X) (f : X → ℝ) : ℝ :=
  sSup (f '' K) - sInf (f '' K)

end CannonScalarLimit

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_WeightedOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set Topology
open Set Metric Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology

namespace CannonMagnification

open CannonPacking Set Metric Filter Topology

def normalized {X : Type*} [TopologicalSpace X] (f : X → ℝ)
    (h : X ≃ₜ X) (x : X) (σ : ℝ) (z : X) : ℝ := (f (h.symm z)-f x)/σ

lemma continuous_normalized {X : Type*} [TopologicalSpace X] (f : X → ℝ)
    (hf : Continuous f) (h : X ≃ₜ X) (x : X) (σ : ℝ) : Continuous (normalized f h x σ) :=
  ((hf.comp h.symm.continuous).sub continuous_const).div_const σ

end CannonMagnification

open Set Filter Topology Metric

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_Domain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set Topology
open Set Metric Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric

open Set Metric Topology

namespace CannonMagnification

open CannonPacking Set Metric Filter Topology

def onDomain {X : Type*} [TopologicalSpace X] {Ω : Set X} (f : C(Ω,ℝ)) (x : X) : ℝ :=
  by classical exact if h : x ∈ Ω then f ⟨x,h⟩ else 0

end CannonMagnification

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_Words
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric
open Set Metric Topology

namespace CannonStabilizer

open Set

def words {G : Type*} [Group G] [DecidableEq G] (a b : G) : ℕ → Finset G
  | 0 => {1}
  | n+1 => (words a b n).image (a*·) ∪ (words a b n).image (b*·)

def ContractingDirection {G X : Type*} [Group G] [MulAction G X]
    [TopologicalSpace X] (E : Subgroup G) (b x : X) : Prop :=
  ∀ U : Set X, IsOpen U → x ∈ U → ∀ V : Set X, IsOpen V → b ∈ V →
    ∃ g ∈ E, MapsTo (g • ·) Vᶜ U

end CannonStabilizer

namespace CannonStabilizer

open CannonMagnification

@[instance_reducible] def homAction {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) : MulAction G X where
  smul g x := ρ g x
  one_smul x := by change ρ 1 x = x; rw [map_one]; rfl
  mul_smul g h x := by change ρ (g*h) x = ρ g (ρ h x); rw [map_mul]; rfl

end CannonStabilizer

open Set unitInterval

namespace CannonVariation

open Filter Topology Metric

def NonconstantAt {X : Type*} [TopologicalSpace X] (F : X → ℝ) (x : X) : Prop :=
  ¬ ∀ᶠ y in 𝓝 x, F y = F x

end CannonVariation

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_VisualSynchronousPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
open Set Topology

namespace CannonRelease

open CannonVisual Filter Topology Finset

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G)
  {δ : ℕ}

local instance visualSynchronousGraphBallDecidable : ∀ p : Prop, Decidable p :=
  Classical.propDecidable

end CannonRelease

namespace CannonRelease

open CannonVisual Finset

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G)
  {δ : ℕ}

local instance visualSynchronousInverseRayDecidable : ∀ p : Prop, Decidable p :=
  Classical.propDecidable

end CannonRelease

end

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Uniformization_LayerFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
namespace CannonUniformization
open Set Metric unitInterval

noncomputable section
variable {X : Type*} [MetricSpace X]

def layerFamily (o : X) (s : ℝ) : Set (Set X) :=
  {A | ∃ u v : X, ∃ p : Path u v, A = range p ∧
    dist u o = s ∧ dist v o = 2*s ∧ ∀ t, dist (p t) o ∈ Icc s (2*s)}

end
end CannonUniformization

end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Uniformization_EventualRelativeShrink
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
noncomputable section
namespace CannonRealization
open Set Filter Topology Metric

variable {X Y : Type*} [MetricSpace X] [CompactSpace X]
  [MetricSpace Y] [CompactSpace Y]

def EventualRelativeShrink (F : ℕ → C(X,Y)) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ τ : ℝ, 0<τ ∧ ∀ R : ℝ, 0<R →
    ∀ᶠ n : ℕ in atTop, ∀ x a b : X,
      dist x a ≤ τ*R → R ≤ dist x b →
        dist (F n x) (F n a) ≤ ε*dist (F n x) (F n b)

def RelativeShrink (f : X → Y) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ τ : ℝ, 0<τ ∧ ∀ x a b : X,
    dist x a ≤ τ*dist x b →
      dist (f x) (f a) ≤ ε*dist (f x) (f b)

end CannonRealization

end
end
section
noncomputable section
open Set Metric

namespace CannonRealization
open Set Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def WeakQS (f : X → Y) (H : ℝ) : Prop :=
  ∀ x a b, dist x a ≤ dist x b → dist (f x) (f a) ≤ H*dist (f x) (f b)

end CannonRealization

end
end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Distinct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
noncomputable section
namespace CannonQM
open Metric
open scoped NNReal

def Distinct {X : Type*} (x y z w : X) : Prop :=
  x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w

def crossRatio {X : Type*} [MetricSpace X] (x y z w : X) : ℝ≥0 :=
  nndist x y * nndist z w / (nndist x w * nndist y z)

abbrev Distortion := ℝ≥0 ≃o ℝ≥0

lemma distortion_zero (η : Distortion) : η 0 = 0 := η.map_bot

def reciprocal (η : Distortion) : Distortion where
  toFun t := (η t⁻¹)⁻¹
  invFun t := (η.symm t⁻¹)⁻¹
  left_inv t := by simp
  right_inv t := by simp
  map_rel_iff' := by
    intro x y
    change (η x⁻¹)⁻¹ ≤ (η y⁻¹)⁻¹ ↔ x ≤ y
    by_cases hx : x=0
    · subst x
      simp only [inv_zero,distortion_zero,zero_le]
    by_cases hy : y=0
    · subst y
      have hη : η x⁻¹ ≠ 0 := by
        rw [← distortion_zero η]
        exact fun hh => hx (inv_eq_zero.mp (η.injective hh))
      simp only [inv_zero,distortion_zero,le_zero_iff,inv_eq_zero]
      exact ⟨fun hh => (hη hh).elim,fun hh => (hx hh).elim⟩
    have hxpos : 0 < x := pos_iff_ne_zero.mpr hx
    have hypos : 0 < y := pos_iff_ne_zero.mpr hy
    have hηx : 0 < η x⁻¹ := by simpa only [distortion_zero] using η.strictMono (inv_pos.mpr hxpos)
    have hηy : 0 < η y⁻¹ := by simpa only [distortion_zero] using η.strictMono (inv_pos.mpr hypos)
    rw [inv_le_inv₀ hηx hηy,η.le_iff_le,inv_le_inv₀ hypos hxpos]

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

def Controlled (f : X → Y) (η : Distortion) : Prop :=
  ∀ x y z w, Distinct x y z w →
    crossRatio (f x) (f y) (f z) (f w) ≤ η (crossRatio x y z w)

def QuasiMobius (f : X → Y) : Prop := ∃ η : Distortion, Controlled f η

end CannonQM

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_PreservesProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
noncomputable section

namespace CannonMetricQC

def WeakQS (f : ℂ → ℂ) (H : ℝ) : Prop :=
  ∀ x y z, dist x y ≤ dist x z → dist (f x) (f y) ≤ H*dist (f x) (f z)
end CannonMetricQC

end
end
end
section
noncomputable section
namespace CannonMetricQC
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

def DensityOne (s : Set ℂ) (x : ℂ) : Prop :=
  Tendsto (fun r : ℝ => volume (s ∩ closedBall x r)/volume (closedBall x r))
    (𝓝[>] 0) (𝓝 1)

end CannonMetricQC

namespace CannonMetricQC
open Set Metric MeasureTheory Filter
open scoped Topology NNReal ENNReal

def PointwiseLip (f : ℂ → ℂ) (x : ℂ) : Prop :=
  ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ ∀ y, dist x y < r → dist (f x) (f y) ≤ C*dist x y

def lipPiece (f : ℂ → ℂ) (n : ℕ) : Set ℂ :=
  {x | ‖x‖ ≤ (n:ℝ)+1 ∧ ∀ y, dist x y < 1/((n:ℝ)+1) →
    dist (f x) (f y) ≤ (n:ℝ)*dist x y}

end CannonMetricQC

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_ImageArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
noncomputable section
namespace CannonMetricQC
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

def imageArea (f : ℂ ≃ₜ ℂ) : Measure ℂ := volume.map f.symm

end CannonMetricQC

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_CutoffBump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace CannonMetricQC
open Set Metric Filter
open scoped Topology ContDiff NNReal

def cutoffBump (R : ℝ) : ContDiffBump (0:ℂ) :=
    {rIn := max R 0+1
     rOut := max R 0+2
     rIn_pos := by linarith [le_max_right R 0]
     rIn_lt_rOut := by linarith}

def smoothCutoff (R : ℝ) (x : ℂ) : ℂ := (cutoffBump R x:ℂ)

end CannonMetricQC

noncomputable section
noncomputable section

namespace CannonMetricQC
open MeasureTheory Set Metric Filter Function ContinuousLinearMap
open scoped Topology Convolution ENNReal NNReal

def mollifier (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / ((n : ℝ)+1)
  rOut := 2 / ((n : ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply (div_lt_div_iff_of_pos_right (by positivity)).mpr; norm_num

def mollify (μ : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  (mollifier n).normed volume ⋆[lsmul ℝ ℝ, volume] μ

end CannonMetricQC

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_RectCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace CannonRealPlane

def RectCrossing (u : ℝ × ℝ → ℝ) (c : ℝ) (A B δ : ℝ) : Prop :=
  ∃ a b : ℝ, a ∈ Icc A B ∧ b ∈ Icc A B ∧ δ ≤ b-a ∧
    ((∀ t ∈ Icc a b, ∃ y ∈ Icc A B, u (t,y)=c) ∨
     (∀ t ∈ Icc a b, ∃ x ∈ Icc A B, u (x,t)=c))

end CannonRealPlane

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Topology_PlaneBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace CannonPlane
open Set Metric MeasureTheory

def planeBox (R : ℝ) : Set ℂ := Complex.equivRealProdCLM ⁻¹' (Icc (-R) R ×ˢ Icc (-R) R)

end CannonPlane

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace CannonPlane

def annularCutoff (r R : ℝ) (z : ℂ) : ℝ :=
  Real.smoothTransition (Real.log (‖z‖/r)/Real.log (R/r))

end CannonPlane

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Topology_CenteredHomeomorph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Topology

namespace CannonPlane

def centeredHomeomorph (F : ℂ ≃ₜ ℂ) (x : ℂ) : ℂ ≃ₜ ℂ where
  toFun z := F (z+x)-F x
  invFun w := F.symm (w+F x)-x
  left_inv z := by simp
  right_inv w := by simp
  continuous_toFun := (F.continuous.comp (continuous_id.add continuous_const)).sub continuous_const
  continuous_invFun := (F.symm.continuous.comp (continuous_id.add continuous_const)).sub continuous_const

@[simp] lemma centeredHomeomorph_apply (F : ℂ ≃ₜ ℂ) (x z : ℂ) :
    centeredHomeomorph F x z = F (z+x)-F x := rfl

@[simp] lemma centeredHomeomorph_symm_apply (F : ℂ ≃ₜ ℂ) (x z : ℂ) :
    (centeredHomeomorph F x).symm z = F.symm (z+F x)-x := rfl

end CannonPlane

noncomputable section
open Set Metric Filter Topology

namespace CannonPlane

def UniformRelativeControl {ι : Type*} (F : ι → ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ i x a b, b ≠ x →
    dist a x < η*dist b x → dist (F i a) (F i x) < ε*dist (F i b) (F i x)

end CannonPlane

noncomputable section
open Set Filter Topology Metric

namespace CannonPlane

def homeomorphMap (F : ℂ ≃ₜ ℂ) : C(ℂ,ℂ) := ⟨F,F.continuous⟩

end CannonPlane

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Beltrami_Increment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
namespace CannonOrientation
open Set Topology
open scoped ComplexConjugate

def HasIncrement (g : ℝ → ℂ) (w : ℂ) : Prop :=
  ∃ L : ℝ → ℂ, Continuous L ∧ (∀ t, Complex.exp (L t)=g t) ∧ L 1-L 0=w

def circle (t : ℝ) : ℂ := Complex.exp ((2*Real.pi*t:ℝ)*Complex.I)

@[fun_prop] lemma continuous_circle : Continuous circle := by unfold circle; fun_prop
@[simp] lemma circle_zero : circle 0=1 := by simp [circle]
@[simp] lemma circle_one : circle 1=1 := by simp [circle]

def clip (s : ℝ) : ℝ := max 0 (min 1 s)
@[fun_prop] lemma continuous_clip : Continuous clip := by unfold clip; fun_prop
@[simp] lemma clip_zero : clip 0=0 := by norm_num [clip]
@[simp] lemma clip_one : clip 1=1 := by norm_num [clip]
end CannonOrientation

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_BoundedCrossRatios
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
noncomputable section
namespace CannonQM
open Set Metric Filter Bornology Topology

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

def BoundedCrossRatios (f : X → Y) : Prop :=
  ∀ T : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ x y z w : X, Distinct x y z w →
    (crossRatio x y z w : ℝ) ≤ T → (crossRatio (f x) (f y) (f z) (f w) : ℝ) ≤ C

end CannonQM

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_SphereMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
noncomputable section

noncomputable section

namespace CannonMetricQC
open scoped ComplexOrder

def derivativeMatrix (A : ℂ →L[ℝ] ℂ) : Fin 4 → ℝ :=
  ![(A 1).re,(A Complex.I).re,(A 1).im,(A Complex.I).im]
def derivativeDet (A : ℂ →L[ℝ] ℂ) : ℝ :=
  (A 1).re*(A Complex.I).im-(A Complex.I).re*(A 1).im

end CannonMetricQC

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_FiniteB
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
noncomputable section
open Set Filter Topology
open scoped OnePoint

noncomputable section
open Set Filter Topology

namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
end CannonMobius

end
end
end
end
end
end

end OAI
end


