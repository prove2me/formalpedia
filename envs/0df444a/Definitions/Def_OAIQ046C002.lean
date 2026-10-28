-- Prove2me | Definitions.Def_OAIQ046C002
-- name    : OAIQ046C002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:45:29.707662+00:00
-- url     : https://prove2.me/theorems/cef49d3c-1aed-408f-a64f-8615a5076bbe
-- title:
--   Definitions bundle OAIQ046C002 of the split of OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CannonRelease.cannon`, carved from OpenAI's openai/math development (OpenAI, *A Modulus Proof of Cannon's Conjecture (result family 246)*, OpenAI Math Release, September 23, 2026, result family 246, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 134 declarations of OpenAI's Lean: 75 definitions, 5 instances and 54 theorems. The definitions and types are `OAI.CannonH3.conformalActionExtension`, `OAI.CannonH3.extensionHom`, `OAI.CannonH3.interior`, `OAI.CannonH3.lift`, `OAI.CannonH3.pairedH3`, `OAI.CannonMagnification.weightedOscillation`, `OAI.CannonMetricQC.derivativeForm`, `OAI.CannonMobius.GoodDifferentials`, `OAI.CannonMobius.PreservesProducts`, `OAI.CannonMobius.affineMatrix`, `OAI.CannonMobius.center`, `OAI.CannonMobius.centerEnergy`, `OAI.CannonMobius.chartOne`, `OAI.CannonMobius.chartZero`, `OAI.CannonMobius.finiteA`, `OAI.CannonMobius.finiteB`, `OAI.CannonMobius.finiteCenterRaw`, `OAI.CannonMobius.finiteNormalizer`, `OAI.CannonMobius.generalMatrix`, `OAI.CannonMobius.halfInclusion`, `OAI.CannonMobius.markedChart`, `OAI.CannonMobius.matrixCenterRaw`, `OAI.CannonMobius.matrixEnergy`, `OAI.CannonMobius.matrixFun`, `OAI.CannonMobius.matrixHomeomorph`, `OAI.CannonMobius.normalizer`, `OAI.CannonMobius.numerator`, `OAI.CannonMobius.ratio`, `OAI.CannonMobius.rescale`, `OAI.CannonMobius.restrictedSphereAction`, `OAI.CannonMobius.roundChart`, `OAI.CannonMobius.rowNorm`, `OAI.CannonMobius.sendToInfty`, `OAI.CannonMobius.sphereDerivative`, `OAI.CannonMobius.sphereMeasure`, `OAI.CannonMobius.spherePermAction`, `OAI.CannonMobius.standard`, `OAI.CannonMobius.std`, `OAI.CannonMobius.swapColumns`, `OAI.CannonNode.LiteralTransitions` and 35 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/Cannon, in whole or in part: `Cannon_Actions_Height`, `Cannon_Boundary_BoundaryBasedRay`, `Cannon_Boundary_BoundaryDist`, `Cannon_Boundary_BoundaryHomeomorph`, `Cannon_Boundary_Thin`, `Cannon_Boundary_VisualSynchronousPrefix`, `Cannon_CirclePacking_AngleGradient`, `Cannon_CirclePacking_Det`, `Cannon_CirclePacking_OrientedArea`, `Cannon_CirclePacking_Radius`, `Cannon_Conformal_Chart`, `Cannon_Conformal_FiniteB`, `Cannon_Conformal_MarkedChart`, `Cannon_Conformal_Normalizer`, `Cannon_Conformal_PreservesProducts`, `Cannon_Conformal_RestrictedSphereAction`, `Cannon_Conformal_Round`, `Cannon_Conformal_Sphere`, `Cannon_Conformal_SphereMeasure`, `Cannon_Conformal_SphereTile`, `Cannon_Energy_RawFunction`, `Cannon_Energy_Square`, `Cannon_Flows_FlowPuncture`, `Cannon_Flows_Node`, `Cannon_Flows_State`, `Cannon_Flows_WeightedOscillation`, `Cannon_PlanarGraphs_Support`, `Cannon_ScalarLimits_Words`.
--
--   **Imports.** It imports the published bundle `Def_CannonGeometricAction`; the bundles `OAIQ046C000` and `OAIQ046C001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.CannonEmbeddedArc.Arc.packing_relative_modulus_cost`, `OAI.CannonMobius.sphere_action_straightening`, `OAI.CannonRelease.boundary_holder_scalar_impossible`, `OAI.CannonRelease.boundary_modulus_subexponential`, `OAI.CannonRelease.boundary_no_record_flow`, `OAI.CannonRelease.boundary_packing_relative_tests`, `OAI.CannonRelease.boundary_quasiMobius_uniformizer`, `OAI.CannonRelease.boundary_record_data`, `OAI.CannonRelease.boundary_record_scalar_limit`, `OAI.CannonRelease.boundary_uniform_circle_packing` and `OAI.CannonRelease.boundary_uniform_controlled_faces`; the proofs of `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.disk_disjoint_of_interior`, `OAI.CannonEmbeddedArc.Arc.intrinsic_developed_faces`, `OAI.CannonEmbeddedArc.Arc.packing_relative_modulus_cost`, `OAI.CannonEmbeddedArc.Arc.proper_facial_bound`, `OAI.CannonMobius.sphere_action_straightening`, `OAI.CannonPlanarEuler.triangular_counts`, `OAI.CannonRelease.boundary_holder_scalar_impossible`, `OAI.CannonRelease.boundary_modulus_subexponential`, `OAI.CannonRelease.boundary_no_record_flow`, `OAI.CannonRelease.boundary_packing_relative_tests`, `OAI.CannonRelease.boundary_quasiMobius_uniformizer`, `OAI.CannonRelease.boundary_record_data`, `OAI.CannonRelease.boundary_record_scalar_limit`, `OAI.CannonRelease.boundary_uniform_circle_packing`, `OAI.CannonRelease.boundary_uniform_controlled_faces` and `OAI.CannonRelease.cannon`.
-- source:
--   OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 246; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Modulus-Proof-of-Cannons-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/Cannon at commit adc7f12

import Mathlib
import Definitions.Def_CannonGeometricAction
import Definitions.Def_OAIQ046C000
import Definitions.Def_OAIQ046C001

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Sphere
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def reflection : S ≃ₜ S :=
  Complex.conjCLE.toHomeomorph.onePointCongr.trans CannonMobius.inversion

end CannonSphereReflection

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_AngleGradient
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
open Set Filter Topology

noncomputable section

variable {I : Type*} [Fintype I]

def segmentGradient (x s : ℝ) (t : ℝ) := (s-x)*angleGradient (angleMove x s t)

end
end CannonPackingGeometry

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_Support
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

noncomputable section
namespace CannonPlanarEuler
open Set Topology unitInterval CannonEmbeddedArc CannonEmbeddedArc.Arc CannonFaceIncidence

variable {ι : Type*} [DecidableEq ι]
def support (F : ι → Arc ℂ) (S : Finset ι) : Set ℂ := ⋃ i∈S,range (F i)
def faces (F : ι → Arc ℂ) (S : Finset ι) : ℕ :=
  Nat.card (ConnectedComponents ((support F S)ᶜ : Set ℂ))
end CannonPlanarEuler

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
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_OrientedArea
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def Folds {V:Type*} (K:ℂ≃ᵢℂ) (c d:V→ℂ) (S T:Set V) (u v:V) : Prop :=
  K (c u)=d u ∧ K (c v)=d v ∧
    ∀ w∈S,w≠u → w≠v → ∀ z∈T,z≠u → z≠v →
      orientedArea (d u) (d v) (K (c w))*orientedArea (d u) (d v) (d z)<0

end CannonPackingGeometry

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_Det
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def TriInterior (a b c p : ℂ) : Prop :=
  0<orientedArea a b p*orientedArea a b c ∧
  0<orientedArea b c p*orientedArea b c a ∧
  0<orientedArea c a p*orientedArea c a b

end CannonPackingGeometry

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_SphereTile
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
open Set Filter Topology
open scoped OnePoint

def std (i : Fin 3) : Sphere := ![∞,((0:ℂ):Sphere),((1:ℂ):Sphere)] i
lemma std_injective : Function.Injective std := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [std]

def standard : Triple := ⟨std,std_injective⟩

lemma exists_finite_normalizer (t : Triple) (ht : ∀ i, t.val i ≠ ∞) :
    ∃ f : Sphere ≃ₜ Sphere, f ∈ biholomorphic ∧ tripleMap f standard=t := by
  let p : Fin 3 → ℂ := fun i => coordinate (t.val i)
  have hp (i : Fin 3) : (p i:Sphere)=t.val i := coe_coordinate (ht i)
  have hinj : Function.Injective p := by
    intro i j h
    apply t.property
    rw [← hp i,← hp j,h]
  have h10 : p 1-p 0 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (1:Fin 3) ≠ 0) (hinj h))
  have h20 : p 2-p 0 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (2:Fin 3) ≠ 0) (hinj h))
  let b := (p 1-p 0)⁻¹
  let a := (p 2-p 0)⁻¹-b
  have ha : a ≠ 0 := by
    intro h
    have he : (p 2-p 0)⁻¹=(p 1-p 0)⁻¹ := sub_eq_zero.mp h
    have he' := inv_injective he
    exact (by decide : (2:Fin 3) ≠ 1) (hinj (sub_left_injective he'))
  refine ⟨affine 1 (p 0) one_ne_zero*inversion*affine a b ha,
    biholomorphic.mul_mem (biholomorphic.mul_mem (affine_biholomorphic _ _ _) inversion_biholomorphic)
      (affine_biholomorphic _ _ _),?_⟩
  apply Subtype.ext
  funext i
  fin_cases i
  · change affine 1 (p 0) one_ne_zero (inv ∞)=t.val 0
    rw [inv_infty,affine_coe]
    simpa using hp 0
  · change affine 1 (p 0) one_ne_zero (inv (affine a b ha (0:ℂ)))=t.val 1
    rw [affine_coe]
    simp only [mul_zero,zero_add]
    rw [inv_coe (inv_ne_zero h10),affine_coe]
    simpa [b] using hp 1
  · change affine 1 (p 0) one_ne_zero (inv (affine a b ha (1:ℂ)))=t.val 2
    rw [affine_coe]
    have he : a*1+b=(p 2-p 0)⁻¹ := by dsimp [a]; ring
    rw [he,inv_coe (inv_ne_zero h20),affine_coe]
    simpa using hp 2

lemma exists_pole_avoiding (t : Triple) : ∃ p : ℂ, ∀ i, t.val i ≠ (p:Sphere) := by
  obtain ⟨p,hp⟩ := (Set.finite_range (fun i : Fin 3 => coordinate (t.val i))).exists_notMem
  refine ⟨p,?_⟩
  intro i hi
  apply hp
  refine ⟨i,?_⟩
  change coordinate (t.val i)=p
  rw [hi,coordinate_coe]

lemma exists_triple_normalizer (t : Triple) :
    ∃ f : Sphere ≃ₜ Sphere, f ∈ biholomorphic ∧ tripleMap f standard=t := by
  obtain ⟨p,hp⟩ := exists_pole_avoiding t
  let N : Sphere ≃ₜ Sphere := inversion*affine 1 (-p) one_ne_zero
  have hN : N ∈ biholomorphic := biholomorphic.mul_mem inversion_biholomorphic
    (affine_biholomorphic _ _ _)
  have hNp : N (p:Sphere)=∞ := by
    change inv (affine 1 (-p) one_ne_zero p)=∞
    rw [affine_coe]
    simp only [one_mul,add_neg_cancel,inv_zero]
  have hfin (i : Fin 3) : (tripleMap N t).val i ≠ ∞ :=
    fun he => hp i (N.injective (he.trans hNp.symm))
  obtain ⟨f,hf,he⟩ := exists_finite_normalizer (tripleMap N t) hfin
  refine ⟨N⁻¹*f,biholomorphic.mul_mem (biholomorphic.inv_mem hN) hf,?_⟩
  rw [tripleMap_mul,he]
  apply Subtype.ext
  funext i
  exact N.symm_apply_apply _

end CannonMobius

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Actions_Height
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
namespace CannonH3
open CannonRelease Set Topology

lemma dist_coords (x y : HyperbolicThree) :
    hyperbolicDist x y=Real.arcosh (distArg (coords x) (coords y)) := by
  unfold hyperbolicDist distArg
  congr 1
  have he : ‖(coords x).1-(coords y).1‖^2=(x.val 0-y.val 0)^2+(x.val 1-y.val 1)^2 := by
    rw [Complex.sq_norm]
    change (x.val 0-y.val 0)*(x.val 0-y.val 0)+(x.val 1-y.val 1)*(x.val 1-y.val 1)=_
    ring
  rw [he]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change 1+((x.val 0-y.val 0)^2+((x.val 1-y.val 1)^2+(x.val 2-y.val 2)^2))/(2*x.val 2*y.val 2)=
    1+(((x.val 0-y.val 0)^2+(x.val 1-y.val 1)^2)+(x.val 2-y.val 2)^2)/(2*x.val 2*y.val 2)
  ring

def lift (f : Half ≃ₜ Half) (hf : ∀ x y, distArg (f x) (f y)=distArg x y) : H3Isom :=
  ⟨(coords.trans f).trans coords.symm,by
    intro x y
    rw [dist_coords,dist_coords]
    simpa only [Homeomorph.trans_apply,Homeomorph.apply_symm_apply] using congrArg Real.arcosh (hf (coords x) (coords y))⟩

end CannonH3

noncomputable section
open Set Filter Topology
open scoped OnePoint

namespace CannonH3
open Set

def pairedH3 : paired →* CannonRelease.H3Isom where
  toFun u := lift u.val.2 u.property.2
  map_one' := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro x
    change coords.symm (coords x)=x
    exact coords.symm_apply_apply x
  map_mul' u v := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro x
    change coords.symm (u.val.2 (v.val.2 (coords x)))=
      coords.symm (u.val.2 (coords (coords.symm (v.val.2 (coords x)))))
    rw [coords.apply_symm_apply]

def extensionHom : boundaryGroup →* CannonRelease.H3Isom :=
  pairedH3.comp (MonoidHom.ofInjective boundaryProjection_injective).symm.toMonoidHom

end CannonH3

noncomputable section
open Set Filter Topology

namespace CannonH3
open scoped OnePoint

def conformalActionExtension {G : Type*} [Group G]
    (σ : G →* (Boundary ≃ₜ Boundary))
    (hσ : ∀ g, σ g ∈ CannonMobius.biholomorphic ∨
      boundaryReflection*σ g ∈ CannonMobius.biholomorphic) : G →* CannonRelease.H3Isom :=
  extensionHom.comp (σ.codRestrict boundaryGroup (fun g => conformal_or_anticonformal_mem (hσ g)))

end CannonH3

namespace CannonH3

def interior (f : boundaryGroup) : Half ≃ₜ Half :=
  (coords.symm.trans (extensionHom f).val).trans coords
end CannonH3

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
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_Radius
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
open Filter Topology

namespace CannonNode

lemma radius_pos (ell : ℝ) (k : ℕ) : 0 < radius ell k := Real.exp_pos _

lemma radius_add (ell : ℝ) (k d : ℕ) : radius ell (k+d) = radius ell d*radius ell k := by
  simp only [radius,Nat.cast_add, mul_add,Real.exp_add]
  ring

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
-- module Solutions.OAIQ046_CN.Cannon_Boundary_Thin
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
open Set

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G] (D : CayleyData G)

instance basedRay_compactSpace : CompactSpace (BasedRay D) := by
  apply isCompact_iff_compactSpace.mp
  exact CannonGraph.compact_ray_space D.connected
    (CannonGraph.finite_cayley_neighbors D.generators) 1

instance boundary_compactSpace : CompactSpace (Boundary D) :=
  inferInstanceAs (CompactSpace (Quotient (raySetoid D)))

lemma raySetoid_isClosed (hthin : D.ThinTriangles) :
    IsClosed {p : BasedRay D × BasedRay D | (raySetoid D).r p.1 p.2} := by
  obtain ⟨δ,hδ⟩ := hthin
  have hr : {p : BasedRay D × BasedRay D | (raySetoid D).r p.1 p.2} =
    ⋂ n : ℕ, {p | D.graph.dist (p.1.val n) (p.2.val n) ≤ 2*δ} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hp
      exact CannonGraph.asymptotic_rays_uniform D.connected hδ p.1.val p.2.val
        p.1.property.2 p.2.property.2 (p.1.property.1.trans p.2.property.1.symm) hp
    · intro hp
      exact ⟨2*δ,hp⟩
  rw [hr]
  apply isClosed_iInter
  intro n
  have h₁ : Continuous (fun p : BasedRay D × BasedRay D => p.1.val n) :=
    (continuous_apply n).comp (continuous_subtype_val.comp continuous_fst)
  have h₂ : Continuous (fun p : BasedRay D × BasedRay D => p.2.val n) :=
    (continuous_apply n).comp (continuous_subtype_val.comp continuous_snd)
  exact (isClosed_discrete {k : ℕ | k ≤ 2*δ}).preimage
    ((continuous_of_discreteTopology : Continuous (fun p : G × G => D.graph.dist p.1 p.2)).comp
      (h₁.prodMk h₂))

 theorem boundary_t2Space (hthin : D.ThinTriangles) : T2Space (Boundary D) :=
  CannonBoundary.quotient_t2_of_closed (raySetoid D) (raySetoid_isClosed D hthin)

end CannonRelease

namespace CannonRelease
open Set Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G)

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma CayleyData.dist_mul_left (g x y : G) :
    D.graph.dist (g*x) (g*y) = D.graph.dist x y :=
  CannonGraph.iso_dist D.connected (D.leftIso g) x y

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma Asymptotic.mul_left {r s : ℕ → G} (h : Asymptotic D r s) (g : G) :
    Asymptotic D (fun n => g*r n) (fun n => g*s n) := by
  obtain ⟨C,hC⟩ := h
  exact ⟨C,fun n => by rw [D.dist_mul_left]; exact hC n⟩

variable (hthin : D.ThinTriangles)

include hthin in
lemma exists_translate_ray (g : G) (r : BasedRay D) :
    ∃ s : BasedRay D, Asymptotic D s.val (fun n => g*r.val n) := by
  obtain ⟨δ,hδ⟩ := hthin
  have hg : ∀ i j, D.graph.dist (g*r.val i) (g*r.val j) = Nat.dist i j :=
    fun i j => (D.dist_mul_left g _ _).trans (r.property.2 i j)
  obtain ⟨s,hs,hr,ha⟩ := CannonGraph.exists_rebased_ray D.connected
    (CannonGraph.finite_cayley_neighbors D.generators) hδ (fun n => g*r.val n)
    hg 1
  exact ⟨⟨s,hs,hr⟩,_,ha⟩

def translateRay (g : G) (r : BasedRay D) : BasedRay D :=
  (exists_translate_ray D hthin g r).choose

lemma translateRay_spec (g : G) (r : BasedRay D) :
    Asymptotic D (translateRay D hthin g r).val (fun n => g*r.val n) :=
  (exists_translate_ray D hthin g r).choose_spec

lemma translateRay_respects (g : G) {r s : BasedRay D}
    (h : (raySetoid D).r r s) :
    (raySetoid D).r (translateRay D hthin g r) (translateRay D hthin g s) :=
  Asymptotic.trans D (Asymptotic.trans D (translateRay_spec D hthin g r)
    (Asymptotic.mul_left D h g)) (Asymptotic.symm D (translateRay_spec D hthin g s))

local instance instSetoidBasedRay_r036316_1 : Setoid (BasedRay D) := raySetoid D
def boundaryTranslate (g : G) : Boundary D → Boundary D :=
  Quotient.map (translateRay D hthin g) (by
    intro r s hrs
    exact translateRay_respects D hthin g hrs)

lemma boundaryTranslate_one (x : Boundary D) : boundaryTranslate D hthin 1 x = x := by
  induction x using Quotient.inductionOn with
  | h r =>
    apply Quotient.sound
    change Asymptotic D (translateRay D hthin 1 r).val r.val
    simpa only [one_mul] using translateRay_spec D hthin 1 r

lemma boundaryTranslate_mul (g h : G) (x : Boundary D) :
    boundaryTranslate D hthin (g*h) x =
      boundaryTranslate D hthin g (boundaryTranslate D hthin h x) := by
  induction x using Quotient.inductionOn with
  | h r =>
    apply Quotient.sound
    have h₁ := Asymptotic.mul_left D (translateRay_spec D hthin h r) g
    have h₂ := Asymptotic.trans D (translateRay_spec D hthin g (translateRay D hthin h r)) h₁
    exact Asymptotic.trans D (translateRay_spec D hthin (g*h) r)
      (Asymptotic.symm D (by simpa only [mul_assoc] using h₂))

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
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

include hthin in
lemma translated_relation_closed (g : G) :
    IsClosed {p : BasedRay D × BasedRay D |
      Asymptotic D p.2.val (fun n => g*p.1.val n)} := by
  obtain ⟨δ,hδ⟩ := hthin
  have he : {p : BasedRay D × BasedRay D |
      Asymptotic D p.2.val (fun n => g*p.1.val n)} =
      ⋂ n : ℕ, {p | D.graph.dist (p.2.val n) (g*p.1.val n) ≤ 3*D.graph.dist 1 g + 4*δ} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hp
      have hh := CannonGraph.asymptotic_rays_different_bases_uniform D.connected
        (CannonGraph.finite_cayley_neighbors D.generators) hδ p.2.val
        (fun n => g*p.1.val n) p.2.property.2
        (fun i j => (D.dist_mul_left g _ _).trans (p.1.property.2 i j)) hp
      simpa only [p.1.property.1, p.2.property.1, mul_one, CayleyData.graph] using hh
    · intro hp
      exact ⟨_,hp⟩
  rw [he]
  apply isClosed_iInter
  intro n
  have h₁ : Continuous (fun p : BasedRay D × BasedRay D => p.2.val n) :=
    (continuous_apply n).comp (continuous_subtype_val.comp continuous_snd)
  have h₂ : Continuous (fun p : BasedRay D × BasedRay D => g*p.1.val n) :=
    (continuous_of_discreteTopology : Continuous (fun x : G => g*x)).comp
      ((continuous_apply n).comp (continuous_subtype_val.comp continuous_fst))
  exact (isClosed_discrete {k : ℕ | k ≤ 3*D.graph.dist 1 g + 4*δ}).preimage
    ((continuous_of_discreteTopology : Continuous (fun p : G × G => D.graph.dist p.1 p.2)).comp
      (h₁.prodMk h₂))

attribute [local instance] OAI.CannonRelease.instSetoidBasedRay_1
lemma boundaryTranslate_graph_closed (g : G) :
    IsClosed {p : Boundary D × Boundary D | boundaryTranslate D hthin g p.1 = p.2} := by
  let _ : T2Space (Boundary D) := boundary_t2Space D hthin
  let _ : T2Space (Quotient (raySetoid D)) := boundary_t2Space D hthin
  let _ : T2Space (Quotient (inferInstance : Setoid (BasedRay D))) := boundary_t2Space D hthin
  have he : {p : Boundary D × Boundary D | boundaryTranslate D hthin g p.1 = p.2} =
      Prod.map (Quotient.mk' : BasedRay D → Boundary D) Quotient.mk' ''
      {p : BasedRay D × BasedRay D | Asymptotic D p.2.val (fun n => g*p.1.val n)} := by
    ext p
    constructor
    · intro hp
      obtain ⟨r,hr⟩ := Quotient.mk'_surjective p.1
      obtain ⟨s,hs⟩ := Quotient.mk'_surjective p.2
      have hq : (raySetoid D).r (translateRay D hthin g r) s := by
        apply Quotient.exact
        change boundaryTranslate D hthin g (Quotient.mk' r) = Quotient.mk' s
        rw [hr, hs]
        exact hp
      refine ⟨(r,s),?_,Prod.ext hr hs⟩
      exact Asymptotic.trans D (Asymptotic.symm D hq) (translateRay_spec D hthin g r)
    · rintro ⟨⟨r,s⟩,hrs,rfl⟩
      exact Quotient.sound (Asymptotic.trans D (translateRay_spec D hthin g r)
        (Asymptotic.symm D hrs))
  rw [he]
  exact ((translated_relation_closed D hthin g).isCompact.image
    (continuous_quotient_mk'.prodMap continuous_quotient_mk')).isClosed

lemma boundaryTranslate_continuous (g : G) : Continuous (boundaryTranslate D hthin g) := by
  apply continuous_iff_isClosed.mpr
  intro F hF
  have he : boundaryTranslate D hthin g ⁻¹' F =
      Prod.fst '' ({p : Boundary D × Boundary D | boundaryTranslate D hthin g p.1 = p.2} ∩
        (Set.univ ×ˢ F)) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x,boundaryTranslate D hthin g x),⟨rfl,trivial,hx⟩,rfl⟩
    · rintro ⟨⟨x,y⟩,⟨hxy,_,hy⟩,rfl⟩
      change boundaryTranslate D hthin g x ∈ F
      change boundaryTranslate D hthin g x = y at hxy
      rwa [hxy]
  rw [he]
  exact isClosedMap_fst_of_compactSpace _
    ((boundaryTranslate_graph_closed D hthin g).inter (isClosed_univ.prod hF))

def boundaryHomeomorph (g : G) : Boundary D ≃ₜ Boundary D where
  toFun := boundaryTranslate D hthin g
  invFun := boundaryTranslate D hthin g⁻¹
  left_inv x := by
    rw [← boundaryTranslate_mul, inv_mul_cancel, boundaryTranslate_one]
  right_inv x := by
    rw [← boundaryTranslate_mul, mul_inv_cancel, boundaryTranslate_one]
  continuous_toFun := boundaryTranslate_continuous D hthin g
  continuous_invFun := boundaryTranslate_continuous D hthin g⁻¹

def boundaryAction : G →* (Boundary D ≃ₜ Boundary D) where
  toFun := boundaryHomeomorph D hthin
  map_one' := by
    ext x
    exact boundaryTranslate_one D hthin x
  map_mul' g h := by
    ext x
    exact boundaryTranslate_mul D hthin g h x

end CannonRelease

namespace CannonVisual
open SimpleGraph Filter Topology
open scoped Topology NNReal

variable {V : Type*} {G : SimpleGraph V} {o : V}

noncomputable def decay (ε : ℝ) (r s : Ray G o) (n : ℕ) : ℝ≥0 :=
  ⟨Real.exp (-ε * (CannonGraph.product2 (G := G) o (r.val n) (s.val n))), (Real.exp_pos _).le⟩

noncomputable def preDist (ε : ℝ) (r s : Ray G o) : ℝ≥0 := ⨅ n : ℕ, decay ε r s n

lemma preDist_le_decay (ε : ℝ) (r s : Ray G o) (n : ℕ) :
    preDist ε r s ≤ decay ε r s n := ciInf_le (OrderBot.bddBelow _) n

lemma decay_comm (ε : ℝ) (r s : Ray G o) (n : ℕ) : decay ε r s n = decay ε s r n := by
  apply NNReal.coe_injective
  change Real.exp _ = Real.exp _
  rw [CannonGraph.product2_comm (o := o) (x := r.val n) (y := s.val n)]

lemma preDist_comm (ε : ℝ) (r s : Ray G o) : preDist ε r s = preDist ε s r := by
  simp only [preDist, decay_comm ε r s]

lemma decay_antitone (hG : G.Connected) {ε : ℝ} (hε : 0 ≤ ε) (r s : Ray G o) :
    Antitone (decay ε r s) := by
  intro i j hij
  change Real.exp (-ε * (CannonGraph.product2 (G := G) o (r.val j) (s.val j))) ≤
    Real.exp (-ε * (CannonGraph.product2 (G := G) o (r.val i) (s.val i)))
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hε)
  have h := CannonGraph.product2_ray_mono hG r.val s.val r.property.2 s.property.2
    (r.property.1.trans s.property.1.symm) hij
  rw [r.property.1] at h
  exact_mod_cast h

lemma product2_self (r : Ray G o) (n : ℕ) :
    CannonGraph.product2 (G := G) o (r.val n) (r.val n) = 2*n := by
  have hr := r.property.2 0 n
  rw [r.property.1] at hr
  simp only [CannonGraph.product2, SimpleGraph.dist_self, Nat.sub_zero, hr, Nat.dist_zero_left]
  omega

lemma preDist_self {ε : ℝ} (hε : 0 < ε) (r : Ray G o) : preDist ε r r = 0 := by
  apply NNReal.coe_injective
  let f : ℕ → ℝ := fun n => Real.exp (-(2*ε) * (n : ℝ))
  have ht : Tendsto f atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [Function.comp_def, neg_mul] using tendsto_neg_atTop_atBot.comp
      (Filter.Tendsto.const_mul_atTop (by positivity : 0 < 2*ε)
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hb : ∀ n, (preDist ε r r : ℝ) ≤ f n := by
    intro n
    have h := preDist_le_decay ε r r n
    change (preDist ε r r : ℝ) ≤ Real.exp (-ε * (CannonGraph.product2 (G := G) o (r.val n) (r.val n))) at h
    rw [product2_self, Nat.cast_mul, Nat.cast_ofNat] at h
    simpa only [f, neg_mul, mul_neg, mul_assoc, mul_comm, mul_left_comm] using h
  have hh : (preDist ε r r : ℝ) ≤ 0 := ge_of_tendsto ht (Filter.Eventually.of_forall hb)
  exact le_antisymm hh (NNReal.coe_nonneg _)

end CannonVisual

namespace CannonVisual
open SimpleGraph Filter Topology
open scoped Topology NNReal

variable {V : Type*} {G : SimpleGraph V} {o : V}

lemma product2_four (hG : G.Connected) {δ : ℕ} (hthin : CannonGraph.Thin G δ)
    (o x₁ x₂ x₃ x₄ : V) :
    min (CannonGraph.product2 (G := G) o x₁ x₂)
      (min (CannonGraph.product2 (G := G) o x₂ x₃) (CannonGraph.product2 (G := G) o x₃ x₄)) ≤
      CannonGraph.product2 (G := G) o x₁ x₄ + 2*(8*δ+6) := by
  have h₁ := CannonGraph.product2_hyperbolic hG hthin o x₁ x₂ x₄
  have h₂ := CannonGraph.product2_hyperbolic hG hthin o x₂ x₃ x₄
  omega

lemma decay_four (hG : G.Connected) {δ : ℕ} (hthin : CannonGraph.Thin G δ)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : Real.exp (ε * (2*(8*δ+6) : ℕ)) ≤ 2)
    (r₁ r₂ r₃ r₄ : Ray G o) (n : ℕ) :
    decay ε r₁ r₄ n ≤ 2 * max (decay ε r₁ r₂ n) (max (decay ε r₂ r₃ n) (decay ε r₃ r₄ n)) := by
  let p₁₂ : ℝ := CannonGraph.product2 (G := G) o (r₁.val n) (r₂.val n)
  let p₂₃ : ℝ := CannonGraph.product2 (G := G) o (r₂.val n) (r₃.val n)
  let p₃₄ : ℝ := CannonGraph.product2 (G := G) o (r₃.val n) (r₄.val n)
  let p₁₄ : ℝ := CannonGraph.product2 (G := G) o (r₁.val n) (r₄.val n)
  have hp : min p₁₂ (min p₂₃ p₃₄) ≤ p₁₄ + (2*(8*δ+6) : ℕ) := by
    dsimp [p₁₂, p₂₃, p₃₄, p₁₄]
    exact_mod_cast product2_four hG hthin o (r₁.val n) (r₂.val n) (r₃.val n) (r₄.val n)
  have hh : -ε*p₁₄ ≤ ε*(2*(8*δ+6) : ℕ) + -ε * min p₁₂ (min p₂₃ p₃₄) := by
    nlinarith
  have hh' := Real.exp_le_exp.mpr hh
  rw [Real.exp_add, exp_neg_mul_min hε, exp_neg_mul_min hε] at hh'
  exact hh'.trans (mul_le_mul_of_nonneg_right hsmall (by positivity))

lemma tendsto_decay (hG : G.Connected) {ε : ℝ} (hε : 0 ≤ ε) (r s : Ray G o) :
    Tendsto (decay ε r s) atTop (𝓝 (preDist ε r s)) :=
  tendsto_atTop_ciInf (decay_antitone hG hε r s) (OrderBot.bddBelow _)

lemma preDist_four (hG : G.Connected) {δ : ℕ} (hthin : CannonGraph.Thin G δ)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : Real.exp (ε * (2*(8*δ+6) : ℕ)) ≤ 2)
    (r₁ r₂ r₃ r₄ : Ray G o) :
    preDist ε r₁ r₄ ≤ 2 * max (preDist ε r₁ r₂) (max (preDist ε r₂ r₃) (preDist ε r₃ r₄)) := by
  apply le_of_tendsto_of_tendsto (tendsto_decay hG hε r₁ r₄)
    (((tendsto_decay hG hε r₁ r₂).max ((tendsto_decay hG hε r₂ r₃).max
      (tendsto_decay hG hε r₃ r₄))).const_mul 2)
  exact Filter.Eventually.of_forall (decay_four hG hthin hε hsmall r₁ r₂ r₃ r₄)

@[instance_reducible]
noncomputable def rayPseudoMetric (δ : ℕ) : PseudoMetricSpace (Ray G o) :=
  PseudoMetricSpace.ofPreNNDist (preDist (visualExponent δ))
    (preDist_self (visualExponent_pos δ)) (preDist_comm (visualExponent δ))

lemma visual_distance_le (δ : ℕ) (r s : Ray G o) :
    @dist _ (rayPseudoMetric (G := G) (o := o) δ).toDist r s ≤ preDist (visualExponent δ) r s :=
  PseudoMetricSpace.dist_ofPreNNDist_le _ _ _ _ _

lemma preDist_le_twice_visual_distance (hG : G.Connected) {δ : ℕ} (hthin : CannonGraph.Thin G δ)
    (r s : Ray G o) :
    (preDist (visualExponent δ) r s : ℝ) ≤ 2 * @dist _ (rayPseudoMetric δ).toDist r s :=
  PseudoMetricSpace.le_two_mul_dist_ofPreNNDist _ _ _
    (preDist_four hG hthin (visualExponent_pos δ).le (visualExponent_small δ)) _ _

end CannonVisual

namespace CannonVisual
open SimpleGraph Filter Topology CannonGraph
open scoped Topology NNReal

variable {V : Type*} {G : SimpleGraph V} {o : V}

lemma product2_ray_sum (hG : G.Connected) (r s : Ray G o) (n : ℕ) :
    product2 (G := G) o (r.val n) (s.val n) + G.dist (r.val n) (s.val n) = 2*n := by
  have hr := r.property.2 0 n
  have hs := s.property.2 0 n
  rw [r.property.1, Nat.dist_zero_left] at hr
  rw [s.property.1, Nat.dist_zero_left] at hs
  simpa only [hr, hs, two_mul] using product2_add_dist hG o (r.val n) (s.val n)

lemma product2_le_of_separated (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    (r s : Ray G o) {k : ℕ} (hsep : 2*δ < G.dist (r.val k) (s.val k)) (n : ℕ) :
    product2 (G := G) o (r.val n) (s.val n) ≤ 2*k+2*δ := by
  by_cases hk : k ≤ n
  · by_contra hn
    let p := raySegment r.val r.property.2 n
    let q := (raySegment s.val s.property.2 n).copy
      (s.property.1.trans r.property.1.symm) rfl
    have hp : p.length = G.dist (r.val 0) (r.val n) := by
      simp [p, r.property.2, Nat.dist]
    have hq : q.length = G.dist (r.val 0) (s.val n) := by
      have h := s.property.2 0 n
      rw [s.property.1] at h
      simpa [q, r.property.1, Nat.dist] using h.symm
    have hkp : k ≤ p.length := by simpa [p] using hk
    have hkq : k ≤ q.length := by simpa [q] using hk
    have hsum := product2_ray_sum hG r s n
    have hnear := fellow_travel_below_product hG hthin p q hp hq hkp hkq (by
      rw [r.property.2, r.property.1]
      have hs := s.property.2 0 n
      rw [s.property.1, Nat.dist_zero_left] at hs
      rw [hs, Nat.dist_zero_left]
      omega)
    have hnear' : G.dist (r.val k) (s.val k) ≤ 2*δ := by
      simpa only [p, q, Walk.getVert_copy, raySegment_getVert _ _ hk] using hnear
    omega
  · have hp := product2_le_twice_left hG o (r.val n) (s.val n)
    have hr := r.property.2 0 n
    rw [r.property.1, Nat.dist_zero_left] at hr
    rw [hr] at hp
    omega

lemma preDist_pos_of_separated (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    {ε : ℝ} (hε : 0 ≤ ε) (r s : Ray G o) {k : ℕ}
    (hsep : 2*δ < G.dist (r.val k) (s.val k)) : 0 < preDist ε r s := by
  let a : ℝ≥0 := ⟨Real.exp (-ε*(2*k+2*δ : ℕ)), (Real.exp_pos _).le⟩
  have ha : 0 < a := Real.exp_pos _
  refine ha.trans_le (le_ciInf fun n => ?_)
  change Real.exp _ ≤ Real.exp _
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hε)
  exact_mod_cast product2_le_of_separated hG hthin r s hsep n

lemma preDist_zero_of_bounded (hG : G.Connected) {ε : ℝ} (hε : 0 < ε)
    (r s : Ray G o) (hbounded : ∃ C : ℕ, ∀ n, G.dist (r.val n) (s.val n) ≤ C) :
    preDist ε r s = 0 := by
  obtain ⟨C,hC⟩ := hbounded
  apply NNReal.coe_injective
  have hb : ∀ n : ℕ, (preDist ε r s : ℝ) ≤ Real.exp (ε*C) * Real.exp (-(2*ε)*(n:ℝ)) := by
    intro n
    have hp := product2_ray_sum hG r s n
    have hpn : (product2 (G := G) o (r.val n) (s.val n) : ℝ) + (C : ℝ) ≥ 2*(n:ℝ) := by
      exact_mod_cast (show 2*n ≤ product2 (G := G) o (r.val n) (s.val n)+C by have := hC n; omega)
    have hh : -ε*(product2 (G := G) o (r.val n) (s.val n) : ℝ) ≤ ε*C + -(2*ε)*(n:ℝ) := by
      nlinarith
    have hle : (preDist ε r s : ℝ) ≤ (decay ε r s n : ℝ) := preDist_le_decay ε r s n
    exact hle.trans (by
      change Real.exp _ ≤ _
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hh)
  have ht := Filter.Tendsto.const_mul (Real.exp (ε*C)) (tendsto_exp_linear hε)
  simp only [mul_zero] at ht
  exact le_antisymm (ge_of_tendsto ht (Filter.Eventually.of_forall hb)) (NNReal.coe_nonneg _)

theorem preDist_zero_iff_bounded (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    {ε : ℝ} (hε : 0 < ε) (r s : Ray G o) :
    preDist ε r s = 0 ↔ ∃ C : ℕ, ∀ n, G.dist (r.val n) (s.val n) ≤ C := by
  constructor
  · intro h
    refine ⟨2*δ,fun n => ?_⟩
    by_contra hn
    have hp := preDist_pos_of_separated hG hthin hε.le r s (Nat.lt_of_not_ge hn)
    rw [h] at hp
    exact (lt_irrefl _ hp)
  · exact preDist_zero_of_bounded hG hε r s

theorem visual_distance_zero_iff_bounded (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    (r s : Ray G o) :
    @dist _ (rayPseudoMetric δ).toDist r s = 0 ↔
      ∃ C : ℕ, ∀ n, G.dist (r.val n) (s.val n) ≤ C := by
  rw [← preDist_zero_iff_bounded hG hthin (visualExponent_pos δ) r s]
  constructor
  · intro h
    have hp := preDist_le_twice_visual_distance hG hthin r s
    rw [h, mul_zero] at hp
    exact NNReal.coe_eq_zero.mp (le_antisymm hp (NNReal.coe_nonneg _))
  · intro h
    have hp := visual_distance_le δ r s
    rw [h, NNReal.coe_zero] at hp
    let := rayPseudoMetric (G := G) (o := o) δ
    exact le_antisymm hp dist_nonneg

end CannonVisual

namespace CannonVisual
open SimpleGraph Filter Topology CannonGraph
open scoped Topology NNReal

variable {V : Type*} {G : SimpleGraph V} {o : V}

def raySetoid (hG : G.Connected) (o : V) : Setoid (Ray G o) where
  r r s := ∃ C : ℕ, ∀ n, G.dist (r.val n) (s.val n) ≤ C
  iseqv := by
    constructor
    · intro r
      exact ⟨0,fun n => by simp⟩
    · rintro r s ⟨C,hC⟩
      exact ⟨C,fun n => by rw [SimpleGraph.dist_comm]; exact hC n⟩
    · rintro r s t ⟨C,hC⟩ ⟨E,hE⟩
      exact ⟨C+E,fun n => (@Connected.dist_triangle _ G (r.val n) (s.val n) (t.val n) hG).trans
        (Nat.add_le_add (hC n) (hE n))⟩

def MetricBoundary (G : SimpleGraph V) (o : V) (hG : G.Connected) := ULift.{0} (Quotient (raySetoid hG o))

noncomputable def boundaryDist (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    (x y : MetricBoundary G o hG) : ℝ :=
  Quotient.liftOn₂ x.down y.down (fun r s => @dist _ (rayPseudoMetric δ).toDist r s) (by
    intro r₁ s₁ r₂ s₂ hr hs
    let := rayPseudoMetric (G := G) (o := o) δ
    have hr₀ := (visual_distance_zero_iff_bounded hG hthin r₁ r₂).mpr hr
    have hs₀ := (visual_distance_zero_iff_bounded hG hthin s₁ s₂).mpr hs
    change dist r₁ s₁ = dist r₂ s₂
    rw [dist_comm r₁ s₁, PseudoMetricSpace.dist_eq_of_dist_zero s₁ hr₀,
      dist_comm s₁ r₂, PseudoMetricSpace.dist_eq_of_dist_zero r₂ hs₀])

@[instance_reducible]
noncomputable def boundaryMetricSpace (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ) :
    MetricSpace (MetricBoundary G o hG) where
  dist := boundaryDist hG hthin
  dist_self x := by
    obtain ⟨x⟩ := x
    induction x using Quotient.inductionOn with | h r =>
      exact @dist_self _ (rayPseudoMetric δ) r
  dist_comm x y := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    induction x,y using Quotient.inductionOn₂ with | h r s =>
      exact @dist_comm _ (rayPseudoMetric δ) r s
  dist_triangle x y z := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    obtain ⟨z⟩ := z
    induction x,y,z using Quotient.inductionOn₃ with | h r s t =>
      exact @dist_triangle _ (rayPseudoMetric δ) r s t
  eq_of_dist_eq_zero := by
    intro x y h
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    induction x,y using Quotient.inductionOn₂ with | h r s =>
      exact congrArg ULift.up (Quotient.sound ((visual_distance_zero_iff_bounded hG hthin r s).mp h))

end CannonVisual

namespace CannonVisual
open SimpleGraph Filter Topology CannonGraph
open scoped Topology NNReal

variable {V : Type*} {G : SimpleGraph V} {o : V}

lemma decay_of_agree (ε : ℝ) (r s : Ray G o) {n : ℕ} (h : r.val n = s.val n) :
    (decay ε r s n : ℝ) = Real.exp (-(2*ε)*(n:ℝ)) := by
  change Real.exp _ = _
  rw [← h, product2_self, Nat.cast_mul, Nat.cast_ofNat]
  congr 1
  ring

lemma continuous_boundary_mk [TopologicalSpace V] [DiscreteTopology V]
    (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ) :
    @Continuous (Ray G o) (MetricBoundary G o hG) inferInstance
      (boundaryMetricSpace (o := o) hG hthin).toUniformSpace.toTopologicalSpace (fun r => ULift.up (Quotient.mk'' r)) := by
  let := boundaryMetricSpace (o := o) hG hthin
  apply continuous_iff_continuousAt.mpr
  intro r
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (tendsto_exp_linear (visualExponent_pos δ)).eventually (gt_mem_nhds hε)
  obtain ⟨n,hn⟩ := he.exists
  have hc : Continuous (fun s : Ray G o => s.val n) :=
    (continuous_apply n).comp continuous_subtype_val
  have hopen : IsOpen {s : Ray G o | s.val n = r.val n} :=
    (isOpen_discrete {r.val n}).preimage hc
  filter_upwards [hopen.mem_nhds (show r.val n = r.val n from rfl)] with s hs
  change @dist _ (rayPseudoMetric δ).toDist s r < ε
  have hle : (preDist (visualExponent δ) s r : ℝ) ≤ (decay (visualExponent δ) s r n : ℝ) :=
    preDist_le_decay _ _ _ _
  exact ((visual_distance_le δ s r).trans hle).trans_lt ((decay_of_agree _ s r hs) ▸ hn)

noncomputable def quotientVisualHomeomorph [TopologicalSpace V] [DiscreteTopology V]
    (hG : G.Connected) (hfin : ∀ v, (G.neighborSet v).Finite) {δ : ℕ} (hthin : Thin G δ) :
    @Homeomorph (Quotient (raySetoid hG o)) (MetricBoundary G o hG) inferInstance
      (boundaryMetricSpace (o := o) hG hthin).toUniformSpace.toTopologicalSpace := by
  let := boundaryMetricSpace (o := o) hG hthin
  let : CompactSpace (Ray G o) := isCompact_iff_compactSpace.mp (compact_ray_space hG hfin o)
  let e : Quotient (raySetoid hG o) ≃ MetricBoundary G o hG := Equiv.ulift.symm
  have hc : Continuous e := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact continuous_boundary_mk hG hthin
  exact e.toHomeomorphOfContinuousClosed hc hc.isClosedMap

end CannonVisual

namespace CannonRelease
open CannonGraph CannonVisual

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

@[instance_reducible]
noncomputable def visualMetricSpace : MetricSpace (Boundary D) := by
  let _ : MetricSpace (CannonVisual.MetricBoundary D.graph 1 D.connected) :=
    CannonVisual.boundaryMetricSpace (o := (1:G)) D.connected hδ
  let e : Boundary D ≃ₜ CannonVisual.MetricBoundary D.graph 1 D.connected :=
    CannonVisual.quotientVisualHomeomorph D.connected
      (finite_cayley_neighbors D.generators) hδ
  exact e.isEmbedding.comapMetricSpace e

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
-- module Solutions.OAIQ046_CN.Cannon_Boundary_BoundaryDist
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
open CannonGraph CannonVisual Filter Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

noncomputable abbrev boundaryDist : Boundary D → Boundary D → ℝ :=
  @dist _ (visualMetricSpace D hδ).toDist

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
-- module Solutions.OAIQ046_CN.Cannon_Flows_Node
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
namespace CannonNode

open Set Metric

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ B : ℝ} {kmin : ℕ}

namespace SourceNode

def child (v : SourceNode f x₀ ε ell c₀ B kmin) (D : ℕ) (y : X)
    (hB : 0 ≤ B) (hθ : radius ell D ≤ 1/2)
    (hy : dist y v.center ≤ B*radius ell v.depth)
    (ht : 0 < fraction v.a v.b (lower f y (c₀*radius ell (v.depth+D)))
      (upper f y (c₀*radius ell (v.depth+D)))) :
    SourceNode f x₀ ε ell c₀ B kmin where
  center := y
  depth := v.depth+D
  lowerDepth := v.lowerDepth.trans (Nat.le_add_right _ _)
  a := childLower v.a (lower f y (c₀*radius ell (v.depth+D)))
  b := childUpper v.b (upper f y (c₀*radius ell (v.depth+D)))
  apos := v.apos.trans_le (le_max_left _ _)
  ab := (fraction_pos_iff v.ab).mp ht
  bone := (min_le_left _ _).trans_lt v.bone
  straddle := ⟨le_max_right _ _,min_le_right _ _⟩
  reserve := by
    have hR := radius_pos ell v.depth
    have htR := mul_le_mul_of_nonneg_right hθ hR.le
    have hB' := mul_le_mul_of_nonneg_left htR (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB)
    have htri := dist_triangle y v.center x₀
    rw [radius_add]
    nlinarith only [v.reserve,hy,htri,hB']

end SourceNode

end CannonNode

end

namespace CannonNode

open Set Metric Finset Filter Topology CannonPacking CannonAnnular CannonMagnification

attribute [local instance] Classical.propDecidable

def LiteralTransitions {X : Type*} [MetricSpace X] (f : X → ℝ) (Y : Finset X)
    (c₀ r a b κ H L Qg Qb : ℝ) : Prop :=
  ∃ S : Finset Y,
    (∀ y ∈ S, 0 < fraction a b (lower f y (c₀*r)) (upper f y (c₀*r))) ∧
    (∀ y ∈ S, ∀ z ∈ S, y ≠ z → H*r < dist (y:X) z) ∧
    ∃ p : S → ℝ, (∀ y, 0 < p y) ∧ (∑ y, p y = 1) ∧
    (∀ y, p y ≤ L*fraction a b (lower f (y.val:X) (c₀*r)) (upper f (y.val:X) (c₀*r))) ∧
    ∀ y, p y ≤ (if LiteralGood f Y c₀ r a b κ then Qg else Qb)*
      (fraction a b (lower f (y.val:X) (c₀*r)) (upper f (y.val:X) (c₀*r)))^2

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

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_BoundaryBasedRay
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
open Set Filter Metric Topology
open Set Filter Topology
open Set Filter MeasureTheory Topology
open Set Filter Topology TopologicalSpace Metric
open scoped NNReal ENNReal
open Set Metric

namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification Set Metric Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryBasedRaySetoid : Setoid (BasedRay D) := raySetoid D

def boundaryBasedRay (x : Boundary D) : BasedRay D := Classical.choose (Quotient.exists_rep x)

def boundaryExpansion (x : Boundary D) (k : ℕ) : Boundary D ≃ₜ Boundary D :=
  boundaryHomeomorph D ⟨δ,hδ⟩ ((boundaryBasedRay D x).val k)⁻¹

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
-- module Solutions.OAIQ046_CN.Cannon_Boundary_VisualSynchronousPrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

open CannonGraph CannonVisual Finset

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance visualSynchronousInverseRaySetoid : Setoid (BasedRay D) := raySetoid D

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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Round
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def roundChart : Sphere ≃ₜ Round :=
  planeHyperplane.toHomeomorph.onePointCongr.trans
    (onePointHyperplaneHomeoUnitSphere north_norm)

@[simp] lemma roundChart_coe (z : ℂ) :
    roundChart (z:Sphere)=stereoInvFun north_norm (planeHyperplane z) := rfl

instance sphereMetric : MetricSpace Sphere :=
  roundChart.isEmbedding.comapMetricSpace roundChart

end CannonMobius

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Chart
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

noncomputable section
namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

def chartZero : Sphere ≃ₜ Sphere := affine 4 0 (by norm_num)*inversion
def chartOne : Sphere ≃ₜ Sphere := affine 5 (-1) (by norm_num)*inversion*affine (-1) 1 (by norm_num)

end CannonMobius

end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_MarkedChart
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

def markedChart (i : Fin 3) : Sphere ≃ₜ Sphere:=![1,chartZero,chartOne] i
end CannonMobius

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_Square
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonLevel.instPathConnectedSpaceSquare
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

namespace CannonPlanar

def clampSquare (z : ℝ × ℝ) : Square :=
  (projIcc 0 1 zero_le_one z.1, projIcc 0 1 zero_le_one z.2)

def toComplex (z : Square) : ℂ := (z.1 : ℝ) + (z.2 : ℝ) * Complex.I

end CannonPlanar

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
-- module Solutions.OAIQ046_CN.Cannon_Energy_RawFunction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

namespace CannonRectangle

open CannonGrid CannonCells CannonBands

abbrev Middle := Strip height (1/3) (2/3)

def normalize (z : Middle) : CannonGrid.Square :=
  (z.val.1, ⟨3*(z.val.2:ℝ)-1, by
    have hz := z.property
    change (z.val.2:ℝ) ∈ Icc (1/3:ℝ) (2/3) at hz
    constructor <;> linarith [hz.1,hz.2]⟩)

def leftRight : Set (Set CannonGrid.Square) :=
  {A | ∃ u v : Middle, u.val.1 = 0 ∧ v.val.1 = 1 ∧
    ∃ p : Path u v, A = Subtype.val '' range p}

def topBottom : Set (Set CannonGrid.Square) :=
  {A | ∃ u v : Middle, height u.val = 1/3 ∧ height v.val = 2/3 ∧
    ∃ p : Path u v, A = Subtype.val '' range p}

end CannonRectangle

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
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

namespace CannonNode.SourceConstruction

open Set Metric Finset Filter Topology CannonFlow

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

abbrev step (g : ℕ) (i : Fin (S.flow.size (g+1))) := S.rule.probOf (S.rule.generation S.root g) i

end CannonNode.SourceConstruction

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
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

open CannonCrossEnergy CannonPacking
open Set Metric Filter Topology

def weightedOscillation {X : Type*} [MetricSpace X]
    (f w : X → ℝ) (O : Set X) (r : ℝ) : ℝ :=
  sSup ((fun x => w x * oscillation f (closedBall x r)) '' O)

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
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_Words
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

namespace CannonRelease

open Set Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) (hthin : D.ThinTriangles)

local instance boundaryStabilizerWordsSetoid : Setoid (BasedRay D) := raySetoid D

end CannonRelease

open Set unitInterval

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
-- module Solutions.OAIQ046_CN.Cannon_Flows_FlowPuncture
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
namespace CannonRelease

open CannonGraph CannonVisual CannonApprox CannonNode Set Metric Filter Topology Finset

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowPunctureMeasurableSpace : MeasurableSpace (Boundary D) := borel (Boundary D)

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] {p : ∀ n, ι n → Boundary D} {r : ℕ → ℝ}

def flowPuncture :
    let _ := visualMetricSpace D hδ
    ∀ (T : RecordData (boundaryHomeomorph D ⟨δ,hδ⟩) ι p r)
      {L CE LE : ℝ} {Q : ℕ} (F : FlowSetup T (2*visualExponent δ) L CE LE Q),
    ∀ (g : ℕ), Fin (F.S.flow.size g) → Boundary D := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  intro T L CE LE Q F g i
  exact boundaryExpansion D hδ (F.S.center g i) (F.S.kmin+160*(Q+1)*F.n*g) T.z₀

end CannonRelease

end

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_PreservesProducts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

def PreservesProducts (f : Sphere → Sphere) : Prop := ∀ p : Fin 4 → Sphere,
  dist (f (p 0)) (f (p 1))*dist (f (p 2)) (f (p 3))*(dist (p 0) (p 3)*dist (p 1) (p 2)) =
  dist (p 0) (p 1)*dist (p 2) (p 3)*(dist (f (p 0)) (f (p 3))*dist (f (p 1)) (f (p 2)))

end CannonMobius

end
end
noncomputable section
namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

def sendToInfty (p : Sphere) : Sphere ≃ₜ Sphere := by
  classical
  exact if p=∞ then 1 else inversion*affine 1 (-coordinate p) one_ne_zero

end CannonMobius

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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_SphereMeasure
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
namespace CannonMobius
open Set Filter Topology MeasureTheory
open scoped OnePoint

instance sphereMeasurableSpace : MeasurableSpace Sphere := borel Sphere
instance sphereBorelSpace : BorelSpace Sphere := ⟨rfl⟩

def sphereMeasure : Measure Sphere := volume.map (fun z : ℂ => (z:Sphere))

end CannonMobius

end
end
section
noncomputable section

noncomputable section

namespace CannonMetricQC
open CannonConformal
open scoped ComplexOrder

def derivativeForm (A : ℂ →L[ℝ] ℂ) : Form :=
  ![‖A 1‖^2,(A 1).re*(A Complex.I).re+(A 1).im*(A Complex.I).im,‖A Complex.I‖^2]

end CannonMetricQC

end
end
end
end
noncomputable section
namespace CannonMobius
open Set Filter Topology MeasureTheory CannonMetricQC
open scoped OnePoint

variable {Γ : Type*} [Group Γ]

def spherePermAction (A : Γ →* (Sphere ≃ₜ Sphere)) : Γ →* Equiv.Perm Sphere where
  toFun g := (A g).toEquiv
  map_one' := by ext p; simp
  map_mul' g h := by ext p; simp

def sphereDerivative (f : Sphere ≃ₜ Sphere) (p : Sphere) : ℂ →L[ℝ] ℂ :=
  fderiv ℝ (inChart false false f) (coordinate p)

def GoodDifferentials (A : Γ →* (Sphere ≃ₜ Sphere)) (H : ℝ) (p : Sphere) : Prop :=
  p ≠ ∞ ∧ ∀ g : Γ, A g p ≠ ∞ ∧
    DifferentiableAt ℝ (inChart false false (A g)) (coordinate p) ∧
    Function.Bijective (sphereDerivative (A g) p) ∧
    ∀ u : ℂ, ‖sphereDerivative (A g) p u‖^2 ≤ H^2* |derivativeDet (sphereDerivative (A g) p)| * ‖u‖^2

end CannonMobius

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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_RestrictedSphereAction
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
namespace CannonMobius
open Set Filter Topology MeasureTheory CannonMetricQC CannonConformal
open scoped OnePoint

variable {Γ : Type*} [Group Γ]

def restrictedSphereAction (A : Γ →* (Sphere ≃ₜ Sphere)) (K : Set Sphere)
    (hK : ∀ g p, A g p ∈ K ↔ p ∈ K) : Γ →* Equiv.Perm K where
  toFun g :=
    { toFun := fun p => ⟨A g p,(hK g p).mpr p.property⟩
      invFun := fun p => ⟨A g⁻¹ p,(hK g⁻¹ p).mpr p.property⟩
      left_inv := by intro p; apply Subtype.ext; simp
      right_inv := by intro p; apply Subtype.ext; simp }
  map_one' := by ext p; change A 1 p=p; simp
  map_mul' g h := by ext p; change A (g*h) p=A g (A h p); simp

end CannonMobius

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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Normalizer
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
noncomputable section
open Set Filter Topology
open scoped OnePoint

noncomputable section
open Set Filter Topology

namespace CannonMobius
open Set Filter Topology CannonH3
open scoped OnePoint

def normalizer (t : Triple) : biholomorphic :=
  ⟨(exists_triple_normalizer t).choose,(exists_triple_normalizer t).choose_spec.1⟩

def center (t : Triple) : Half :=
  interior ⟨(normalizer t).val,biholomorphic_mem_boundaryGroup (normalizer t).property⟩ basepoint

end CannonMobius

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
open Set Filter Topology CannonH3
open scoped OnePoint

def finiteB (t : Triple) : ℂ := (coordinate (t.val 1)-coordinate (t.val 0))⁻¹
def finiteA (t : Triple) : ℂ := (coordinate (t.val 2)-coordinate (t.val 0))⁻¹-finiteB t
lemma finiteA_ne_zero (t : Triple) (ht : ∀ i, t.val i ≠ ∞) : finiteA t ≠ 0 := by
  let p : Fin 3 → ℂ := fun i => coordinate (t.val i)
  have hp (i : Fin 3) : (p i:Sphere)=t.val i := coe_coordinate (ht i)
  have hinj : Function.Injective p := by
    intro i j h
    apply t.property
    rw [← hp i,← hp j,h]
  let b := (p 1-p 0)⁻¹
  let a := (p 2-p 0)⁻¹-b
  have ha : a ≠ 0 := by
    intro h
    have he : (p 2-p 0)⁻¹=(p 1-p 0)⁻¹ := sub_eq_zero.mp h
    have he' := inv_injective he
    exact (by decide : (2:Fin 3) ≠ 1) (hinj (sub_left_injective he'))
  exact ha

def finiteNormalizer (t : Triple) (ht : ∀ i, t.val i ≠ ∞) : Sphere ≃ₜ Sphere :=
  affine 1 (coordinate (t.val 0)) one_ne_zero*inversion*affine (finiteA t) (finiteB t) (finiteA_ne_zero t ht)

def finiteCenterRaw (t : Triple) : ℂ × ℝ :=
  (coordinate (t.val 0)+star (finiteB t)/((‖finiteB t‖^2+‖finiteA t‖^2:ℝ):ℂ),
    ‖finiteA t‖/(‖finiteB t‖^2+‖finiteA t‖^2))
end CannonMobius

namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

def ratio (u v : ℂ) : Sphere := if v=0 then ∞ else (u/v:ℂ)
lemma ratio_of_ne {u v : ℂ} (hv : v ≠ 0) : ratio u v=(u/v:ℂ) := ite_eq_right hv
@[simp] lemma ratio_zero (u : ℂ) : ratio u 0=∞ := ite_eq_left rfl
lemma ratio_scale (u v s : ℂ) (hs : s ≠ 0) : ratio (s*u) (s*v)=ratio u v := by
  by_cases hv : v=0
  · simp [hv]
  · rw [ratio_of_ne (mul_ne_zero hs hv),ratio_of_ne hv,mul_div_mul_left _ _ hs]
lemma inv_ratio (u v : ℂ) (huv : u ≠ 0 ∨ v ≠ 0) : inv (ratio u v)=ratio v u := by
  by_cases hv : v=0
  · subst v
    have hu : u ≠ 0 := huv.resolve_right (not_not.mpr rfl)
    rw [ratio_zero,inv_infty,ratio_of_ne hu,zero_div]
  · by_cases hu : u=0
    · subst u
      rw [ratio_of_ne hv,zero_div,inv_zero,ratio_zero]
    · rw [ratio_of_ne hv,ratio_of_ne hu,inv_coe (div_ne_zero hu hv),inv_div]

lemma continuousAt_ratio {X : Type*} [TopologicalSpace X] {u v : X → ℂ} {x : X}
    (hu : ContinuousAt u x) (hv : ContinuousAt v x) (h : u x ≠ 0 ∨ v x ≠ 0) :
    ContinuousAt (fun y => ratio (u y) (v y)) x := by
  by_cases hvx : v x=0
  · have hux : u x ≠ 0 := h.resolve_right (not_not.mpr hvx)
    have hcont : ContinuousAt (fun y => inv ((v y/u y:ℂ):Sphere)) x :=
      continuous_inv.continuousAt.comp (OnePoint.continuous_coe.continuousAt.comp (hv.div hu hux))
    apply hcont.congr_of_eventuallyEq
    filter_upwards [hu.eventually_ne hux] with y hy
    rw [← ratio_of_ne hy,inv_ratio _ _ (Or.inr hy)]
  · have hcont : ContinuousAt (fun y => ((u y/v y:ℂ):Sphere)) x :=
      OnePoint.continuous_coe.continuousAt.comp (hu.div hv hvx)
    apply hcont.congr_of_eventuallyEq
    filter_upwards [hv.eventually_ne hvx] with y hy
    exact ratio_of_ne hy

def matrixFun (M : Mat) (p : Sphere) : Sphere :=
  p.elim (ratio (M 0 0) (M 1 0))
    (fun z => ratio (M 0 0*z+M 0 1) (M 1 0*z+M 1 1))
@[simp] lemma matrixFun_infty (M : Mat) : matrixFun M ∞=ratio (M 0 0) (M 1 0) := rfl
@[simp] lemma matrixFun_coe (M : Mat) (z : ℂ) :
    matrixFun M z=ratio (M 0 0*z+M 0 1) (M 1 0*z+M 1 1) := rfl

def swapColumns (M : Mat) : Mat := !![M 0 1,M 0 0;M 1 1,M 1 0]
lemma matrixFun_inv (M : Mat) (p : Sphere) : matrixFun M (inv p)=matrixFun (swapColumns M) p := by
  induction p using OnePoint.rec with
  | infty => simp [swapColumns]
  | coe z =>
    by_cases hz : z=0
    · simp [hz,swapColumns]
    · rw [inv_coe hz,matrixFun_coe,matrixFun_coe]
      change ratio (M 0 0*z⁻¹+M 0 1) (M 1 0*z⁻¹+M 1 1)=
        ratio (M 0 1*z+M 0 0) (M 1 1*z+M 1 0)
      rw [← ratio_scale _ _ z hz]
      congr 1 <;> field_simp <;> ring

lemma matrix_nonzero (M : Mat) (hM : M.det ≠ 0) (z : ℂ) :
    M 0 0*z+M 0 1 ≠ 0 ∨ M 1 0*z+M 1 1 ≠ 0 := by
  by_contra hh
  push Not at hh
  apply hM
  rw [Matrix.det_fin_two]
  linear_combination M 0 0*hh.2-M 1 0*hh.1
lemma swapColumns_det (M : Mat) : (swapColumns M).det= -M.det := by
  simp [Matrix.det_fin_two,swapColumns]

lemma matrixFun_continuous_finite {X : Type*} [TopologicalSpace X]
    {M : X → Mat} {q : X → Sphere} {x : X} (hM : ContinuousAt M x)
    (hq : ContinuousAt q x) (hn : (M x).det ≠ 0) (hf : q x ≠ ∞) :
    ContinuousAt (fun y => matrixFun (M y) (q y)) x := by
  let c : Sphere → ℂ := fun p => p.elim 0 id
  have hc : ContinuousAt c (q x) := by
    induction h : q x using OnePoint.rec with
    | infty => exact (hf h).elim
    | coe z => exact OnePoint.continuousAt_coe.mpr continuousAt_id
  have hcoord : ContinuousAt (fun y => c (q y)) x := hc.comp hq
  have hentries (i j : Fin 2) : ContinuousAt (fun y => M y i j) x :=
    (continuousAt_pi.mp (continuousAt_pi.mp hM i)) j
  have hr := continuousAt_ratio ((hentries 0 0).mul hcoord |>.add (hentries 0 1))
    ((hentries 1 0).mul hcoord |>.add (hentries 1 1)) (matrix_nonzero (M x) hn (c (q x)))
  apply hr.congr_of_eventuallyEq
  filter_upwards [hq.eventually_ne hf] with y hy
  induction h : q y using OnePoint.rec with
  | infty => exact (hy h).elim
  | coe z => simp only [Pi.add_apply,Pi.mul_apply,h]; rfl

lemma matrixFun_continuous {X : Type*} [TopologicalSpace X]
    {M : X → Mat} {q : X → Sphere} {x : X} (hM : ContinuousAt M x)
    (hq : ContinuousAt q x) (hn : (M x).det ≠ 0) :
    ContinuousAt (fun y => matrixFun (M y) (q y)) x := by
  by_cases hf : q x=∞
  · have hs : ContinuousAt (fun y => swapColumns (M y)) x := by
      apply continuousAt_pi.mpr
      intro i
      apply continuousAt_pi.mpr
      intro j
      fin_cases i <;> fin_cases j <;>
        exact (continuousAt_pi.mp (continuousAt_pi.mp hM _)) _
    have hn' : (swapColumns (M x)).det ≠ 0 := by rw [swapColumns_det]; exact neg_ne_zero.mpr hn
    have hf' : inv (q x) ≠ ∞ := by rw [hf,inv_infty]; exact OnePoint.coe_ne_infty _
    have hh := matrixFun_continuous_finite hs (continuous_inv.continuousAt.comp hq) hn' hf'
    have he : (fun y => matrixFun (swapColumns (M y)) (inv (q y)))=
        (fun y => matrixFun (M y) (q y)) := by
      funext y
      rw [← matrixFun_inv,inv_involutive (q y)]
    change ContinuousAt (fun y => matrixFun (swapColumns (M y)) (inv (q y))) x at hh
    rwa [he] at hh
  · exact matrixFun_continuous_finite hM hq hn hf

end CannonMobius

namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

lemma matrixFun_eq_smul (g : GL (Fin 2) ℂ) (p : Sphere) : matrixFun g.val p=g • p := by
  induction p using OnePoint.rec with
  | infty => exact (OnePoint.smul_infty_eq_ite g).symm
  | coe z => exact OnePoint.smul_some_eq_ite.symm

def matrixHomeomorph (M : Mat) (hM : M.det ≠ 0) : Sphere ≃ₜ Sphere where
  toEquiv := MulAction.toPerm (Matrix.GeneralLinearGroup.mkOfDetNeZero M hM)
  continuous_toFun := by
    change Continuous (fun p : Sphere => Matrix.GeneralLinearGroup.mkOfDetNeZero M hM • p)
    have he : (fun p : Sphere => Matrix.GeneralLinearGroup.mkOfDetNeZero M hM • p)=matrixFun M :=
      funext (fun p => (matrixFun_eq_smul _ p).symm)
    rw [he]
    exact continuous_iff_continuousAt.mpr (fun p => matrixFun_continuous continuousAt_const continuousAt_id hM)
  continuous_invFun := by
    change Continuous (fun p : Sphere => (Matrix.GeneralLinearGroup.mkOfDetNeZero M hM)⁻¹ • p)
    rw [show (fun p : Sphere => (Matrix.GeneralLinearGroup.mkOfDetNeZero M hM)⁻¹ • p)=
      matrixFun (Matrix.GeneralLinearGroup.mkOfDetNeZero M hM)⁻¹.val from
      funext (fun p => (matrixFun_eq_smul _ p).symm)]
    exact continuous_iff_continuousAt.mpr (fun p => matrixFun_continuous continuousAt_const
      continuousAt_id (Matrix.GeneralLinearGroup.det_ne_zero _))
end CannonMobius

namespace CannonMobius
open Set Filter Topology
open CannonH3
open scoped Matrix.Norms.Elementwise

def rowNorm (M : Mat) : ℝ := ‖M 1 0‖^2+‖M 1 1‖^2
def numerator (M : Mat) : ℂ := M 0 0*star (M 1 0)+M 0 1*star (M 1 1)
def matrixCenterRaw (M : Mat) : ℂ × ℝ := (numerator M/(rowNorm M:ℂ),‖M.det‖/rowNorm M)
def matrixEnergy (M : Mat) : ℝ := ‖M 0 0‖^2+‖M 0 1‖^2+‖M 1 0‖^2+‖M 1 1‖^2

def halfInclusion : Half → ℂ × ℝ := fun x => (x.1,x.2.val)

def centerEnergy (x : Half) : ℝ := (‖x.1‖^2+x.2.val^2+1)/x.2.val
end CannonMobius

namespace CannonMobius
open Set Filter Topology CannonH3
open scoped OnePoint Matrix.Norms.Elementwise

def affineMatrix (a b : ℂ) : Mat := !![a,b;0,1]
def generalMatrix (p a b : ℂ) : Mat := !![p*a,p*b+1;a,b]
end CannonMobius

namespace CannonMobius
open Set Filter Topology CannonH3
open scoped OnePoint Matrix.Norms.Elementwise

def rescale (r : ℝ) (M : Mat) : Mat := (r:ℂ) • M
end CannonMobius

end
end
end
end
end
end

end OAI
end


