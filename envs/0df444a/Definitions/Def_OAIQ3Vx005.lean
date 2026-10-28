-- Prove2me | Definitions.Def_OAIQ3Vx005
-- name    : OAIQ3Vx005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:28:58.263372+00:00
-- url     : https://prove2.me/theorems/c01ce8d9-5e94-422e-9f03-6b1caf827831
-- title:
--   Definitions bundle OAIQ3Vx005 of the split of OpenAI, Strongly rational unitary vertex operator algebras and conformal nets
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinimalVertex.main`, carved from OpenAI's openai/math development (OpenAI, *Strongly rational unitary vertex operator algebras and conformal nets*, OpenAI Math Release, September 25, 2026, result family 280, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 50 declarations of OpenAI's Lean: 10 definitions, 1 instance and 39 theorems. The definitions and types are `OAI.StronglyRationalVOA.CircleMobiusGeometry.Group`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.Implements`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.inclusion`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.lifts`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.positiveLift`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.projectiveStandardAction`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.rotation`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.standardAction`, `OAI.StronglyRationalVOA.SmoothCircleDiffeomorphism.action`, `OAI.StronglyRationalVOA.SmoothCircleLift.ofFunction`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory/VertexAlgebra, in whole or in part: `VertexAlgebra_FixedArc`, `VertexAlgebra_GraphCovariance`, `VertexAlgebra_LocalImplementer`, `VertexAlgebra_MobiusAnomaly`, `VertexAlgebra_MobiusExistence`, `VertexAlgebra_MobiusFullGeometry`, `VertexAlgebra_MobiusGeometry`, `VertexAlgebra_MobiusGroup`, `VertexAlgebra_MobiusStandardAction`, `VertexAlgebra_MobiusStandardTopology`, `VertexAlgebra_NetAxioms`, `VertexAlgebra_ObservableScalars`, `VertexAlgebra_ProjectiveTopology`, `VertexAlgebra_RotationConjugateCommutant`, `VertexAlgebra_SmoothTopology`.
--
--   **Imports.** It imports the published bundle `Def_VertexAlgebraNet`; the bundles `OAIQ3Vx000`, `OAIQ3Vx001` and `OAIQ3Vx002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ3Vx007` and `OAIQ3Vx008`.
-- source:
--   OpenAI, Strongly rational unitary vertex operator algebras and conformal nets, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 280; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strongly-rational-unitary-vertex-operator-algebras-and-conformal-nets-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory/VertexAlgebra at commit adc7f12

import Mathlib
import Definitions.Def_VertexAlgebraNet
import Definitions.Def_OAIQ3Vx000
import Definitions.Def_OAIQ3Vx001
import Definitions.Def_OAIQ3Vx002

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ObservableScalars
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter
open UniformSpace Set Filter

open UniformSpace Set
namespace StronglyRationalVOA.ProperCircleArc
lemma isOpen_carrier (I : ProperCircleArc) : IsOpen I.carrier :=
  QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
end StronglyRationalVOA.ProperCircleArc

open UniformSpace Set

open UniformSpace Set

open Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.ProperCircleArc
lemma exists_mem (x : AddCircle (2*Real.pi)) : ∃ I : ProperCircleArc, x ∈ I.carrier := by
  induction x using QuotientAddGroup.induction_on with
  | H t =>
    let I : ProperCircleArc := ⟨t-Real.pi/2,t+Real.pi/2,by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
    exact ⟨I,t,⟨by dsimp [I]; linarith [Real.pi_pos],by dsimp [I]; linarith [Real.pi_pos]⟩,rfl⟩
end StronglyRationalVOA.ProperCircleArc
namespace StronglyRationalVOA.SmoothCircleFunction
local instance instFactLtRealOfNatHMulPi_5 : Fact (0 < 2*Real.pi) := ⟨period_pos⟩

end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace Set Filter
open scoped Topology
namespace StronglyRationalVOA.ProperCircleArc
lemma translate_contains (I : ProperCircleArc) (t : ℝ) {x : AddCircle (2*Real.pi)}
    (hx : x-(t : AddCircle (2*Real.pi)) ∈ I.carrier) : x ∈ (I.translate t).carrier := by
  obtain ⟨s,hs,he⟩ := hx
  refine ⟨s+t,⟨by dsimp [translate]; linarith [hs.1],by dsimp [translate]; linarith [hs.2]⟩,?_⟩
  change ((s+t : ℝ) : AddCircle (2*Real.pi))=x
  change (s : AddCircle (2*Real.pi))=x-(t : AddCircle (2*Real.pi)) at he
  rw [AddCircle.coe_add,he,sub_add_cancel]
end StronglyRationalVOA.ProperCircleArc

open UniformSpace Set

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_RotationConjugateCommutant
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup _root_.OAI.StronglyRationalVOA.SmoothCircleLift.instTopologicalSpace _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter
open UniformSpace Set Filter

open UniformSpace Set

open UniformSpace Set

open scoped ContDiff
namespace StronglyRationalVOA


namespace SmoothCircleLift
lemma shift_periodic (F : SmoothCircleLift) : Function.Periodic (fun t => F t-t) (2*Real.pi) := by
  intro t
  change F (t+2*Real.pi)-(t+2*Real.pi)=F t-t
  rw [F.period]
  ring
lemma integer_shift (F : SmoothCircleLift) (n : ℤ) (t : ℝ) :
    F (t+n*(2*Real.pi))=F t+n*(2*Real.pi) := by
  have h := F.shift_periodic.zsmul n t
  simp only [zsmul_eq_mul] at h
  linarith
end SmoothCircleLift


end StronglyRationalVOA

open UniformSpace
open scoped ContDiff

open scoped ContDiff

open UniformSpace
open scoped ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothTopology
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace StronglyRationalVOA.SmoothCircleLift

lemma unitLift_jet (F : SmoothCircleLift) (k : ℕ) :
    PositiveCircleGeometry.SmoothLift.jet F.unitLift k =
      ContinuousMap.const ℝ ((2*Real.pi)⁻¹*(2*Real.pi)^k) *
        (jet F k).comp ⟨fun x => (2*Real.pi)*x, by fun_prop⟩ := by
  ext x
  change iteratedDeriv k (fun y => F (2*Real.pi*y)/(2*Real.pi)) x = _
  simp_rw [div_eq_mul_inv, mul_comm _ (2*Real.pi)⁻¹]
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (F.smooth.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))]
  change (2*Real.pi)⁻¹*((2*Real.pi)^k*iteratedDeriv k F (2*Real.pi*x)) =
    ((2*Real.pi)⁻¹*(2*Real.pi)^k)*iteratedDeriv k F (2*Real.pi*x)
  ring

lemma jet_mul (F G : SmoothCircleLift) (k : ℕ) :
    jet (F*G) k = ∑ c : OrderedFinpartition k,
      (jet F c.length).comp (jet G 0) * ∏ j, jet G (c.partSize j) := by
  ext x
  change iteratedDeriv k (F ∘ G) x = _
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition F.smooth.contDiffAt G.smooth.contDiffAt
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))]
  simp [jet]



end StronglyRationalVOA.SmoothCircleLift

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ProjectiveTopology
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Filter Set
open scoped Topology
namespace StronglyRationalVOA



instance instTopologicalSpaceSmoothCircleDiffeomorphism : TopologicalSpace SmoothCircleDiffeomorphism := inferInstanceAs
  (TopologicalSpace (SmoothCircleLift ⧸ SmoothCircleLift.circleAction.ker))
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GraphCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
 

lemma onSubmodule_affine_graph (D : Submodule ℂ H) (P Q : Module.End ℂ D)
    (E : H ≃ₗᵢ[ℂ] H) (e : D ≃ₗᵢ[ℂ] D) (he : ∀ z : D, (e z : H)=E z)
    (c : ℂ) (hcov : ∀ z : D, Q (e z)=e (P z)+c • e z)
    (hP : (onSubmodule D P).IsClosable) (hQ : (onSubmodule D Q).IsClosable)
    {x y : H} (hxy : (x,y) ∈ (onSubmodule D P).closure.graph) :
    (E x,E y+c • E x) ∈ (onSubmodule D Q).closure.graph := by
  rw [← hP.graph_closure_eq_closure_graph] at hxy
  have hclosed : IsClosed {p : H × H |
      (E p.1,E p.2+c • E p.1) ∈ (onSubmodule D Q).closure.graph} :=
    hQ.closure_isClosed.preimage ((E.continuous.comp continuous_fst).prodMk
      ((E.continuous.comp continuous_snd).add ((E.continuous.comp continuous_fst).const_smul c)))
  apply (closure_minimal (s := ((onSubmodule D P).graph : Set _)) ?_ hclosed) hxy
  rintro p hp
  obtain ⟨z,hz,hPz⟩ := (onSubmodule D P).mem_graph_iff.mp hp
  have ht : ((z : H),(P z : H))=p := Prod.ext hz hPz
  rw [← ht]
  have h := LinearPMap.le_graph_of_le (onSubmodule D Q).le_closure
    (onSubmodule_mem_graph D Q (e z))
  rw [hcov z] at h
  change ((e z : H),(e (P z) : H)+c • (e z : H)) ∈ _ at h
  rw [he z,he (P z)] at h
  exact h
lemma onSubmodule_affine_graph_iff (D : Submodule ℂ H) (P Q : Module.End ℂ D)
    (E : H ≃ₗᵢ[ℂ] H) (e : D ≃ₗᵢ[ℂ] D) (he : ∀ z : D, (e z : H)=E z)
    (c : ℂ) (hcov : ∀ z : D, Q (e z)=e (P z)+c • e z)
    (hP : (onSubmodule D P).IsClosable) (hQ : (onSubmodule D Q).IsClosable)
    (x y : H) :
    (x,y) ∈ (onSubmodule D P).closure.graph ↔
    (E x,E y+c • E x) ∈ (onSubmodule D Q).closure.graph := by
  constructor
  · exact onSubmodule_affine_graph D P Q E e he c hcov hP hQ
  · intro hxy
    have hei (z : D) : (e.symm z : H)=E.symm z := by
      apply E.injective
      rw [E.apply_symm_apply,← he,e.apply_symm_apply]
    have hci (z : D) : P (e.symm z)=e.symm (Q z)+(-c) • e.symm z := by
      apply e.injective
      rw [map_add,map_smul,e.apply_symm_apply,e.apply_symm_apply,neg_smul,← sub_eq_add_neg]
      have h := hcov (e.symm z)
      rw [e.apply_symm_apply] at h
      exact eq_sub_iff_add_eq.mpr h.symm
    have h := onSubmodule_affine_graph D Q P E.symm e.symm hei (-c) hci hQ hP hxy
    simpa only [map_add,map_smul,E.symm_apply_apply,neg_smul,add_neg_cancel_right] using h
end StronglyRationalVOA.SymmetricOperator

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_LocalImplementer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set
open scoped Topology

namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
variable (φ : SmoothLift)
lemma velocity_zero_of_fixed (t x : ℝ) (hx : φ x=x) : φ.velocity t x=0 := by
  have hi : φ.interpolate t x=x := by dsimp [interpolate]; rw [hx]; ring
  have hinv : φ.inverse t x=x := by simpa only [hi] using φ.inverse_interpolate t x
  simp only [velocity,hinv,hx,sub_self,mul_zero]
end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_FixedArc
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set
namespace StronglyRationalVOA.SmoothCircleLift
 

lemma fixed_arc_deck (F : SmoothCircleLift) (I : ProperCircleArc)
    (hF : ∀ z ∈ I.carrier, F.onCircle z=z) :
    ∃ n : ℤ, ∀ x : ℝ, (x : AddCircle (2*Real.pi)) ∈ I.carrier → F x=x+n*(2*Real.pi) := by
  let S := Ioo I.left I.right
  have hz (x : S) : F x-x ∈ AddSubgroup.zmultiples (2*Real.pi) := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    rw [AddCircle.coe_sub]
    apply sub_eq_zero.mpr
    exact hF _ ⟨x,x.property,rfl⟩
  let D : S → AddSubgroup.zmultiples (2*Real.pi) := fun x => ⟨F x-x,hz x⟩
  have hD : Continuous D := ((F.smooth.continuous.comp continuous_subtype_val).sub
    continuous_subtype_val).subtype_mk hz
  have hl : IsLocallyConstant D := (IsLocallyConstant.iff_continuous D).mpr hD
  let : PreconnectedSpace S := Subtype.preconnectedSpace isPreconnected_Ioo
  let x₀ : S := ⟨(I.left+I.right)/2,by constructor <;> linarith [I.nonempty']⟩
  obtain ⟨n,hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hz x₀)
  simp only [zsmul_eq_mul] at hn
  have he (y : S) : F y-y=n*(2*Real.pi) := by
    exact (congrArg Subtype.val (hl.apply_eq_of_preconnectedSpace y x₀)).trans hn.symm
  refine ⟨n,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := hx
  have hm : x-y ∈ AddSubgroup.zmultiples (2*Real.pi) := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change (y : AddCircle (2*Real.pi))=(x : AddCircle (2*Real.pi)) at hxy
    rw [AddCircle.coe_sub,hxy,sub_self]
  obtain ⟨m,hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  simp only [zsmul_eq_mul] at hm
  have hrep : x=y+m*(2*Real.pi) := by linarith
  rw [hrep,F.integer_shift]
  linarith [he ⟨y,hy⟩]
lemma fixed_arc_normalize (F : SmoothCircleLift) (I : ProperCircleArc)
    (hF : ∀ z ∈ I.carrier, F.onCircle z=z) :
    ∃ G : SmoothCircleLift, G.onCircle=F.onCircle ∧
      ∀ x : ℝ, (x : AddCircle (2*Real.pi)) ∈ I.carrier → G x=x := by
  obtain ⟨n,hn⟩ := F.fixed_arc_deck I hF
  refine ⟨rotation (((-n : ℤ):ℝ)*(2*Real.pi))*F,?_,?_⟩
  · funext z
    rw [onCircle_mul,deck_onCircle]
  · intro x hx
    simp only [mul_apply,rotation_apply,Int.cast_neg,neg_mul,hn x hx]
    ring
end StronglyRationalVOA.SmoothCircleLift

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusGeometry
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped MatrixGroups
namespace StronglyRationalVOA.CircleMobiusGeometry


def Implements (M : SL(2,ℝ)) (F : SmoothCircleLift) : Prop := ∀ x, Rel M x (F x)

lemma derivative_density (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) (x : ℝ) :
    deriv F x=density M (F x) := by
  let a := M 0 0
  let b := M 0 1
  let c := M 1 0
  let d := M 1 1
  have hdet : a*d-b*c=1 := det M
  have hrel (y : ℝ) :
      (a*Real.cos (y/2)+b*Real.sin (y/2))*Real.sin (F y/2)=
      (c*Real.cos (y/2)+d*Real.sin (y/2))*Real.cos (F y/2) := hF y
  let r := (a*Real.cos (x/2)+b*Real.sin (x/2))*Real.cos (F x/2)+
    (c*Real.cos (x/2)+d*Real.sin (x/2))*Real.sin (F x/2)
  obtain ⟨hr1,hr2⟩ := collinear_unit (cos_sq_add_sin_sq (F x/2)) (hrel x)
  change r*Real.cos (F x/2)=a*Real.cos (x/2)+b*Real.sin (x/2) at hr1
  change r*Real.sin (F x/2)=c*Real.cos (x/2)+d*Real.sin (x/2) at hr2
  have hid := (hasDerivAt_id x).div_const (2:ℝ)
  have hfd : HasDerivAt (fun y : ℝ => F y/2) (deriv F x/2) x :=
    (F.differentiable x).hasDerivAt.div_const 2
  have hl := ((hid.cos.const_mul a).add (hid.sin.const_mul b)).mul hfd.sin
  have hr := ((hid.cos.const_mul c).add (hid.sin.const_mul d)).mul hfd.cos
  have he : (fun y => (a*Real.cos (y/2)+b*Real.sin (y/2))*Real.sin (F y/2))=
      (fun y => (c*Real.cos (y/2)+d*Real.sin (y/2))*Real.cos (F y/2)) := funext hrel
  change HasDerivAt (fun y => (a*Real.cos (y/2)+b*Real.sin (y/2))*Real.sin (F y/2)) _ x at hl
  rw [he] at hl
  have hd := hl.unique hr
  dsimp only [id, Pi.add_apply] at hd
  have hd' : r*deriv F x=
      (-c*Real.sin (x/2)+d*Real.cos (x/2))*Real.cos (F x/2)-
      (-a*Real.sin (x/2)+b*Real.cos (x/2))*Real.sin (F x/2) := by
    dsimp only [r]
    linear_combination 2*hd
  have hrd : r^2*deriv F x=1 := by
    calc
      _ = r*(r*deriv F x) := by ring
      _ = (-c*Real.sin (x/2)+d*Real.cos (x/2))*(r*Real.cos (F x/2))-
          (-a*Real.sin (x/2)+b*Real.cos (x/2))*(r*Real.sin (F x/2)) := by rw [hd']; ring
      _ = (a*d-b*c)*(Real.cos (x/2)^2+Real.sin (x/2)^2) := by rw [hr1,hr2]; ring
      _ = 1 := by rw [hdet,cos_sq_add_sin_sq]; ring
  have hrne : r ≠ 0 := by intro h; simp [h] at hrd
  have hb1 : r*(d*Real.cos (F x/2)-b*Real.sin (F x/2))=Real.cos (x/2) := by
    calc
      _ = d*(r*Real.cos (F x/2))-b*(r*Real.sin (F x/2)) := by ring
      _ = (a*d-b*c)*Real.cos (x/2) := by rw [hr1,hr2]; ring
      _ = _ := by rw [hdet,one_mul]
  have hb2 : r*(a*Real.sin (F x/2)-c*Real.cos (F x/2))=Real.sin (x/2) := by
    calc
      _ = a*(r*Real.sin (F x/2))-c*(r*Real.cos (F x/2)) := by ring
      _ = (a*d-b*c)*Real.sin (x/2) := by rw [hr1,hr2]; ring
      _ = _ := by rw [hdet,one_mul]
  have hnorm : r^2*density M (F x)=1 := by
    calc
      _ = (r*(d*Real.cos (F x/2)-b*Real.sin (F x/2)))^2+
          (r*(a*Real.sin (F x/2)-c*Real.cos (F x/2)))^2 := by dsimp [density,a,b,c,d]; ring
      _ = 1 := by rw [hb1,hb2,cos_sq_add_sin_sq]
  exact mul_left_cancel₀ (pow_ne_zero 2 hrne) (hrd.trans hnorm.symm)
lemma push_constant (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) :
    F.pushDensity 1 (fun _ => 1)=density M := by
  funext x
  simp only [SmoothCircleLift.pushDensity,pow_one,mul_one,derivative_density M F hF,
    SmoothCircleLift.apply_inv_apply]
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusAnomaly
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff MatrixGroups
namespace StronglyRationalVOA.CircleMobiusGeometry
lemma density_pos (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) (x : ℝ) :
    0 < density M x := by
  rw [← F.apply_inv_apply x,← derivative_density M F hF]
  exact F.derivative_positive _
lemma inverse_derivative (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) (x : ℝ) :
    deriv (fun x => F⁻¹ x) x=1/density M x := by
  have h := F.derivative_mul F⁻¹ x
  have hid : (fun y => (F*F⁻¹) y)=fun y => y := by simp
  rw [hid,show deriv (fun y : ℝ => y) x=1 from (hasDerivAt_id x).deriv,
    derivative_density M F hF,F.apply_inv_apply] at h
  exact (eq_div_iff (ne_of_gt (density_pos M F hF x))).mpr (by nlinarith)
lemma integral_inverse_density (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) :
    (∫ x in 0..2*Real.pi, 1/density M x)=2*Real.pi := by
  have he : (fun x => 1/density M x)=deriv (fun x => F⁻¹ x) := funext fun x => (inverse_derivative M F hF x).symm
  rw [he,intervalIntegral.integral_deriv_eq_sub (fun x _ => F⁻¹.differentiable x)
    ((contDiff_infty_iff_deriv.mp F⁻¹.smooth).2.continuous.intervalIntegrable _ _)]
  have hp := F⁻¹.period 0
  simp only [zero_add] at hp
  rw [hp]; ring
lemma anomaly_density (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) (x : ℝ) :
    RealCircleCalculus.anomalyDensity (density M) x=
      2*density M x-2*constant M+1/density M x := by
  rw [RealCircleCalculus.anomalyDensity,density_derivative_square]
  field_simp [ne_of_gt (density_pos M F hF x)]
  ring
lemma anomaly_energy (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) :
    RealCircleCalculus.anomalyEnergy (2*Real.pi) (density M)=2*Real.pi := by
  have hd := (density_smooth M).continuous
  have hi : Continuous (fun x => 1/density M x) :=
    continuous_const.div hd (fun x => ne_of_gt (density_pos M F hF x))
  unfold RealCircleCalculus.anomalyEnergy
  simp_rw [anomaly_density M F hF]
  have h2 : IntervalIntegrable (fun x => 2*density M x) volume 0 (2*Real.pi) :=
    (continuous_const.mul hd).intervalIntegrable _ _
  have ha : IntervalIntegrable (fun _ : ℝ => 2*constant M) volume 0 (2*Real.pi) :=
    continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h2.sub ha) (hi.intervalIntegrable _ _),
    intervalIntegral.integral_sub h2 ha,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const,
    integral_density,integral_inverse_density M F hF]
  simp only [sub_zero,smul_eq_mul]
  ring
lemma anomaly_constant_zero (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) (c : ℂ) :
    F.anomaly (fun _ => 1) c=0 := by
  rw [SmoothCircleLift.anomaly,push_constant M F hF,anomaly_energy M F hF]
  have he : RealCircleCalculus.anomalyEnergy (2*Real.pi) (fun _ => 1)=2*Real.pi := by
    simp [RealCircleCalculus.anomalyEnergy,RealCircleCalculus.anomalyDensity]
  rw [he,sub_self,mul_zero,Complex.ofReal_zero,mul_zero]
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusGroup
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped MatrixGroups
namespace StronglyRationalVOA.CircleMobiusGeometry
lemma implements_one : Implements 1 (1 : SmoothCircleLift) := by
  intro x
  simp [Rel,mul_comm]
lemma implements_mul {M N : SL(2,ℝ)} {F G : SmoothCircleLift}
    (hF : Implements M F) (hG : Implements N G) : Implements (M*N) (F*G) := by
  intro x
  have hh := hF (G x)
  have hg := hG x
  obtain ⟨hr1,hr2⟩ := collinear_unit (cos_sq_add_sin_sq (G x/2)) hg
  let r := (N 0 0*Real.cos (x/2)+N 0 1*Real.sin (x/2))*Real.cos (G x/2)+
    (N 1 0*Real.cos (x/2)+N 1 1*Real.sin (x/2))*Real.sin (G x/2)
  change r*Real.cos (G x/2)=N 0 0*Real.cos (x/2)+N 0 1*Real.sin (x/2) at hr1
  change r*Real.sin (G x/2)=N 1 0*Real.cos (x/2)+N 1 1*Real.sin (x/2) at hr2
  change (M 0 0*Real.cos (G x/2)+M 0 1*Real.sin (G x/2))*Real.sin (F (G x)/2)=
    (M 1 0*Real.cos (G x/2)+M 1 1*Real.sin (G x/2))*Real.cos (F (G x)/2) at hh
  simp only [Rel,SmoothCircleLift.mul_apply,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two]
  linear_combination r*hh+(M 1 0*Real.cos (F (G x)/2)-M 0 0*Real.sin (F (G x)/2))*hr1+
    (M 1 1*Real.cos (F (G x)/2)-M 0 1*Real.sin (F (G x)/2))*hr2
lemma implements_inv {M : SL(2,ℝ)} {F : SmoothCircleLift}
    (hF : Implements M F) : Implements M⁻¹ F⁻¹ := by
  intro x
  have h := hF (F⁻¹ x)
  rw [Rel,F.apply_inv_apply] at h
  simp only [Rel,Matrix.SpecialLinearGroup.SL2_inv_expl,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one]
  linear_combination -h
 

def lifts : Subgroup SmoothCircleLift where
  carrier := {F | ∃ M : SL(2,ℝ), Implements M F}
  one_mem' := ⟨1,implements_one⟩
  mul_mem' := by rintro F G ⟨M,hM⟩ ⟨N,hN⟩; exact ⟨M*N,implements_mul hM hN⟩
  inv_mem' := by rintro F ⟨M,hM⟩; exact ⟨M⁻¹,implements_inv hM⟩
lemma implements_rotation (s : ℝ) : Implements (rotationMatrix s) (SmoothCircleLift.rotation s) := by
  intro x
  change (Real.cos (s/2)*Real.cos (x/2)+(-Real.sin (s/2))*Real.sin (x/2))*Real.sin ((x+s)/2)=
    (Real.sin (s/2)*Real.cos (x/2)+Real.cos (s/2)*Real.sin (x/2))*Real.cos ((x+s)/2)
  rw [show (x+s)/2=x/2+s/2 by ring,Real.sin_add,Real.cos_add]
  ring
lemma rotation_mem (s : ℝ) : SmoothCircleLift.rotation s ∈ lifts := ⟨rotationMatrix s,implements_rotation s⟩
def rotation (s : ℝ) : lifts := ⟨SmoothCircleLift.rotation s,rotation_mem s⟩


abbrev Group := lifts ⧸ (SmoothCircleLift.circleAction.comp lifts.subtype).ker
 
def inclusion : Group →* SmoothCircleDiffeomorphism :=
  QuotientGroup.lift (SmoothCircleLift.circleAction.comp lifts.subtype).ker
    ((QuotientGroup.mk' SmoothCircleLift.circleAction.ker).comp lifts.subtype) (by
      intro F hF
      exact (QuotientGroup.eq_one_iff _).mpr hF)
lemma inclusion_injective : Function.Injective inclusion := by
  apply (injective_iff_map_eq_one _).mpr
  intro F
  induction F using QuotientGroup.induction_on with
  | H F =>
    intro h
    apply (QuotientGroup.eq_one_iff F).mpr
    exact (QuotientGroup.eq_one_iff (F:SmoothCircleLift)).mp h
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusExistence
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped MatrixGroups ContDiff

namespace StronglyRationalVOA.SmoothCircleLift
 

def ofFunction (f : ℝ → ℝ) (hs : ContDiff ℝ ∞ f)
    (hp : ∀ x, f (x+2*Real.pi)=f x+2*Real.pi) (hd : ∀ x, 0 < deriv f x) : SmoothCircleLift := by
  let φ : PositiveCircleGeometry.SmoothLift := {
    toFun := fun x => f (2*Real.pi*x)/(2*Real.pi)
    add_one := by intro x; rw [mul_add,mul_one,hp,add_div,div_self (by positivity : (2*Real.pi:ℝ) ≠ 0)]
    smooth := (hs.comp (contDiff_const.mul contDiff_id)).div_const _
    derivative_pos := by
      intro x
      have hh := (((hs.differentiable (by simp) (2*Real.pi*x)).hasDerivAt).comp x
        ((hasDerivAt_id x).const_mul (2*Real.pi))).div_const (2*Real.pi)
      change HasDerivAt (fun x => f (2*Real.pi*x)/(2*Real.pi)) _ x at hh
      rw [hh.deriv]
      have he : deriv f (2*Real.pi*x)*(2*Real.pi*1)/(2*Real.pi)=deriv f (2*Real.pi*x) := by
        field_simp [Real.pi_ne_zero]
      rw [he]
      exact hd _ }
  have hj : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := φ.surjective (y/(2*Real.pi))
    refine ⟨2*Real.pi*x,?_⟩
    exact (div_left_inj' (by positivity : (2*Real.pi:ℝ) ≠ 0)).mp hx
  let e : ℝ ≃o ℝ := StrictMono.orderIsoOfRightInverse f (strictMono_of_deriv_pos hd)
    (Function.surjInv hj) (Function.rightInverse_surjInv hj)
  refine ⟨e,hs,?_,hp⟩
  have hi := PositiveCircleGeometry.parameter_inverse_smooth (fun _ => e)
    (hs.comp contDiff_snd) (fun _ x => (hd x).ne')
  exact hi.comp ((contDiff_const (c := (0:ℝ))).prodMk contDiff_id)
@[simp] lemma ofFunction_apply (f : ℝ → ℝ) (hs : ContDiff ℝ ∞ f)
    (hp : ∀ x, f (x+2*Real.pi)=f x+2*Real.pi) (hd : ∀ x, 0 < deriv f x) (x : ℝ) :
    ofFunction f hs hp hd x=f x := rfl
end StronglyRationalVOA.SmoothCircleLift
namespace StronglyRationalVOA.CircleMobiusGeometry

def positiveLift (M : SL(2,ℝ)) (hp : ∀ x, 0 < dot M x) : SmoothCircleLift :=
  SmoothCircleLift.ofFunction (positiveLiftFun M) (positiveLiftFun_smooth M hp)
    (positiveLiftFun_period M) (derivative_pos_of_rel M _
      ((positiveLiftFun_smooth M hp).differentiable (by simp)) (positiveLiftFun_rel M hp))
lemma implements_positiveLift (M : SL(2,ℝ)) (hp : ∀ x, 0 < dot M x) :
    Implements M (positiveLift M hp) := positiveLiftFun_rel M hp
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusFullGeometry
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped MatrixGroups ContDiff
namespace StronglyRationalVOA.CircleMobiusGeometry


theorem exists_implements (M : SL(2,ℝ)) : ∃ F : SmoothCircleLift, Implements M F := by
  let B := (rotationMatrix (polarAngle M))⁻¹*M
  let G := positiveLift B (polar_dot_positive M)
  refine ⟨SmoothCircleLift.rotation (polarAngle M)*G,?_⟩
  have h := implements_mul (implements_rotation (polarAngle M))
    (implements_positiveLift B (polar_dot_positive M))
  simpa only [B,mul_inv_cancel_left] using h
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusStandardAction
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped MatrixGroups
namespace StronglyRationalVOA.CircleMobiusGeometry

lemma implements_circle_unique {M : SL(2,ℝ)} {F G : SmoothCircleLift}
    (hF : Implements M F) (hG : Implements M G) : F.onCircle=G.onCircle := by
  funext x
  induction x using QuotientAddGroup.induction_on with
  | H x => exact rel_circle_unique M (hF x) (hG x)
lemma group_mk_eq {F G : lifts} (h : (F:SmoothCircleLift).onCircle=(G:SmoothCircleLift).onCircle) :
    (QuotientGroup.mk F : Group)=QuotientGroup.mk G := by
  apply inclusion_injective
  apply QuotientGroup.eq.mpr
  change (SmoothCircleLift.circleAction ((F:SmoothCircleLift)⁻¹*(G:SmoothCircleLift)))=1
  rw [map_mul,map_inv]
  have he : SmoothCircleLift.circleAction (F:SmoothCircleLift)=SmoothCircleLift.circleAction (G:SmoothCircleLift) :=
    Equiv.ext (congrFun h)
  rw [he,inv_mul_cancel]
 
def standardAction : SL(2,ℝ) →* Group where
  toFun M := QuotientGroup.mk (⟨(exists_implements M).choose, M, (exists_implements M).choose_spec⟩ : lifts)
  map_one' := by
    apply group_mk_eq
    exact implements_circle_unique (exists_implements 1).choose_spec implements_one
  map_mul' M N := by
    apply group_mk_eq
    exact implements_circle_unique (exists_implements (M*N)).choose_spec
      (implements_mul (exists_implements M).choose_spec (exists_implements N).choose_spec)
lemma standardAction_eq_mk {M : SL(2,ℝ)} {F : SmoothCircleLift} (hF : Implements M F) :
    standardAction M=QuotientGroup.mk (⟨F,M,hF⟩ : lifts) :=
  group_mk_eq (implements_circle_unique (exists_implements M).choose_spec hF)
lemma center_le_standardAction_ker : Subgroup.center (SL(2,ℝ)) ≤ standardAction.ker := by
  intro M hM
  obtain ⟨r,hr,he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hM
  have h : Implements M (1:SmoothCircleLift) := by
    intro x
    simp only [Rel,← he,Matrix.scalar_apply,Matrix.diagonal_apply,SmoothCircleLift.one_apply]
    simp [mul_assoc,mul_comm,mul_left_comm]
  change standardAction M=1
  exact standardAction_eq_mk h
 

def projectiveStandardAction : PSL(2,ℝ) →* Group :=
  QuotientGroup.lift (Subgroup.center (SL(2,ℝ))) standardAction center_le_standardAction_ker
@[simp] lemma projectiveStandardAction_rotation (t : ℝ) :
    projectiveStandardAction (QuotientGroup.mk (rotationMatrix t))=QuotientGroup.mk (rotation t) :=
  standardAction_eq_mk (implements_rotation t)
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusStandardTopology
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped MatrixGroups Topology ContDiff
namespace StronglyRationalVOA.CircleMobiusGeometry


lemma continuous_of_implements {P : Type*} [TopologicalSpace P] (M : P → SL(2,ℝ))
    (F : P → SmoothCircleLift) (hM : Continuous M)
    (hF : Continuous (fun p : P × ℝ => F p.1 p.2))
    (hrel : ∀ p, Implements (M p) (F p)) : Continuous F := by
  have hj (k : ℕ) : Continuous (fun p : P × ℝ => iteratedDeriv k (F p.1) p.2) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero => exact hF
      | succ k =>
        have he (p : P × ℝ) : iteratedDeriv (k+1) (F p.1) p.2=
            ∑ c : OrderedFinpartition k,
              iteratedDeriv c.length (density (M p.1)) (F p.1 p.2)*
                ∏ j, iteratedDeriv (c.partSize j) (F p.1) p.2 := by
          rw [iteratedDeriv_succ']
          have hd : deriv (F p.1)=density (M p.1) ∘ (F p.1) :=
            funext (derivative_density (M p.1) (F p.1) (hrel p.1))
          rw [hd]
          exact iteratedDeriv_comp_eq_sum_orderedFinpartition
            (density_smooth_standard _).contDiffAt (F p.1).smooth.contDiffAt (by exact_mod_cast (le_top : (k:ℕ∞)≤⊤))
        simp only [he]
        apply continuous_finsetSum
        intro c _
        apply Continuous.mul
        · exact (density_derivative_continuous c.length).comp
            ((hM.comp continuous_fst).prodMk hF)
        · apply continuous_finsetProd
          intro j _
          exact ih _ (Nat.lt_succ_of_le (c.partSize_le j))
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro k
  exact ContinuousMap.continuous_of_continuous_uncurry _ (hj k)



lemma positiveLift_continuous : Continuous (fun M : positiveMatrices => positiveLift M M.property) := by
  apply continuous_of_implements (fun M : positiveMatrices => M.val) _ continuous_subtype_val _
    (fun M => implements_positiveLift M M.property)
  change Continuous (fun p : positiveMatrices × ℝ => positiveLiftFun p.1 p.2)
  dsimp only [positiveLiftFun]
  apply continuous_snd.add
  apply continuous_const.mul
  apply Real.continuous_arctan.comp
  apply Continuous.div
  · dsimp only [cross]
    fun_prop
  · dsimp only [dot]
    fun_prop
  · intro p; exact (p.1.property p.2).ne'
lemma standardAction_continuousAt_one : ContinuousAt standardAction 1 := by
  have hc : Continuous (positiveMatrices.domRestrict standardAction) := by
    have he : positiveMatrices.domRestrict standardAction =
        (fun M : positiveMatrices => QuotientGroup.mk
          (⟨positiveLift M M.property, M, implements_positiveLift M M.property⟩ : lifts)) := by
      funext M
      exact standardAction_eq_mk (implements_positiveLift M M.property)
    rw [he]
    exact (QuotientGroup.isQuotientMap_mk (SmoothCircleLift.circleAction.comp lifts.subtype).ker).continuous.comp
      (positiveLift_continuous.subtype_mk _)
  exact ((continuousWithinAt_iff_continuousAt_domRestrict standardAction one_mem_positiveMatrices).mpr
    hc.continuousAt).continuousAt positiveMatrices_mem_nhds_one
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_NetAxioms
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Topology MatrixGroups
namespace StronglyRationalVOA
namespace SmoothCircleDiffeomorphism
 
def action : SmoothCircleDiffeomorphism →* Equiv.Perm (AddCircle (2*Real.pi)) :=
  QuotientGroup.lift SmoothCircleLift.circleAction.ker SmoothCircleLift.circleAction
    (fun _ h => h)
@[simp] lemma action_mk (F : SmoothCircleLift) (x : AddCircle (2*Real.pi)) :
    action (QuotientGroup.mk F) x=F.onCircle x := rfl
end SmoothCircleDiffeomorphism


end StronglyRationalVOA

end

end OAI
end


