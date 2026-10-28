-- Prove2me | Definitions.Def_OAIQ3Vx012
-- name    : OAIQ3Vx012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:54:53.798033+00:00
-- url     : https://prove2.me/theorems/725daaec-210f-4834-9335-8cc1ee64e06c
-- title:
--   Definitions bundle OAIQ3Vx012 of the split of OpenAI, Strongly rational unitary vertex operator algebras and conformal nets
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinimalVertex.main`, carved from OpenAI's openai/math development (OpenAI, *Strongly rational unitary vertex operator algebras and conformal nets*, OpenAI Math Release, September 25, 2026, result family 280, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 1 definition and 2 theorems. The definitions and types are `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.conformalNetStructure`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory/VertexAlgebra, in whole or in part: [`VertexAlgebra_ConformalNetContinuation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/VertexAlgebra/VertexAlgebra/ConformalNetContinuation.lean), [`VertexAlgebra_RotationImplementer`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/VertexAlgebra/VertexAlgebra/RotationImplementer.lean).
--
--   **Imports.** It imports the published bundle `Def_VertexAlgebraNet`; the bundles `OAIQ3Vx008` and `OAIQ3Vx011` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.MinimalVertex.main`.
-- source:
--   OpenAI, Strongly rational unitary vertex operator algebras and conformal nets, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 280; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strongly-rational-unitary-vertex-operator-algebras-and-conformal-nets-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory/VertexAlgebra at commit adc7f12

import Mathlib
import Definitions.Def_VertexAlgebraNet
import Definitions.Def_OAIQ3Vx008
import Definitions.Def_OAIQ3Vx011

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_RotationImplementer
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)


lemma diffeomorphismImplementer_rotation (hc : A.toVertexAlgebra.C2Cofinite) (s : ℝ)
    (x : Completion V) :
    U.diffeomorphismImplementer hc (SmoothCircleLift.rotation s) x=U.rotation s x := by
  let f := (SmoothCircleLift.rotation s).unitLift.angularStressPath
  let T := U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients
  let τ : ℝ → ℝ := fun t => s*Real.smoothTransition t
  have hτ (t : ℝ) : HasDerivAt τ (s*deriv Real.smoothTransition t) t :=
    (((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) t).hasDerivAt).const_mul s
  have hp (z : U.smoothEnergySpace) (d : ℕ) (v : A.grade d) :
      inner ℂ (U.stressPropagator hc f 1 z) (U.rotation s (v.val:Completion V))=
        inner ℂ (z:Completion V) (v.val:Completion V) := by
    let a : ℝ → ℂ := fun t => Complex.exp ((τ t:ℂ)*(d:ℂ)*Complex.I)
    have ha (t : ℝ) : HasDerivAt a
        (a t*((s*deriv Real.smoothTransition t:ℝ):ℂ)*(d:ℂ)*Complex.I) t := by
      convert (((hτ t).ofReal_comp.mul_const (d:ℂ)).mul_const Complex.I).cexp using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | ring
    have hg : ((v.val:Completion V),(d:ℂ) • (v.val:Completion V)) ∈ U.conformalHamiltonian.graph := by
      exact U.conformalHamiltonian.mem_graph_iff.mpr
        ⟨⟨(v.val:Completion V),U.coe_mem_energyOperator (fun d => d) v.val⟩,rfl,U.energyOperator_grade _ v⟩
    have hd (t : ℝ) : HasDerivAt (fun t =>
        inner ℂ (U.stressPropagator hc f t z) (a t • (v.val:Completion V))) 0 t := by
      have H := (U.stressPropagator_derivative hc f t z).inner ℂ ((ha t).smul_const (v.val:Completion V))
      have he := SymmetricOperator.formalAdjoint_graph_pairing
        (SymmetricOperator.selfAdjoint_formal (U.energyOperator_selfAdjoint (fun d => d)))
        (U.stress_graph_le_hamiltonian hc (U.smoothSmear_graph hc A.conformal_mem
          (SmoothCircleFunction.constant 1).rapid_coefficients (U.stressPropagatorSmooth hc f t z))) hg
      change inner ℂ (T (U.stressPropagatorSmooth hc f t z):Completion V) (v.val:Completion V)=
        inner ℂ (U.stressPropagator hc f t z) ((d:ℂ) • (v.val:Completion V)) at he
      rw [inner_smul_right] at he
      rw [U.rotationPropagatorDerivative hc s t z,inner_smul_left,inner_smul_right,
        inner_smul_right,map_mul,Complex.conj_I,Complex.conj_ofReal] at H
      change HasDerivAt _
        ((a t*((s*deriv Real.smoothTransition t:ℝ):ℂ)*(d:ℂ)*Complex.I)*
          inner ℂ (U.stressPropagator hc f t z) (v.val:Completion V)+
          ((-Complex.I)*((s*deriv Real.smoothTransition t:ℝ):ℂ)) *
          (a t*inner ℂ (T (U.stressPropagatorSmooth hc f t z):Completion V) (v.val:Completion V))) t at H
      rw [he] at H
      convert H using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | ring
    have h := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => (hd t).deriv) 1 0
    have ha0 : a 0=1 := by simp [a,τ]
    have ha1 : a 1=Complex.exp ((s*d:ℝ)*Complex.I) := by simp [a,τ]
    rw [ha0,one_smul,U.stressPropagator_zero,one_apply_eq_self,ha1] at h
    rwa [U.rotation_grade s v]
  have hpf (z : U.smoothEnergySpace) (v : V) :
      inner ℂ (U.stressPropagator hc f 1 z) (U.rotation s (v:Completion V))=
        inner ℂ (z:Completion V) (v:Completion V) := by
    apply A.homogeneous_induction (P := fun v =>
      inner ℂ (U.stressPropagator hc f 1 z) (U.rotation s (v:Completion V))=
        inner ℂ (z:Completion V) (v:Completion V))
    · change inner ℂ _ (U.rotation s (0:Completion V))=inner ℂ _ 0
      simp only [map_zero,inner_zero_right]
    · intro d v hv; exact hp z d ⟨v,hv⟩
    · intro u v hu hv
      simp only [Completion.coe_add,map_add,inner_add_right,hu,hv]
  have hall (z y : Completion V) :
      inner ℂ (U.stressPropagator hc f 1 z) (U.rotation s y)=inner ℂ z y := by
    refine U.smoothEnergySpace_dense.denseRange_val.induction_on z ?_ ?_
    · exact isClosed_eq ((U.stressPropagator hc f 1).continuous.inner continuous_const)
        (continuous_id.inner continuous_const)
    · intro z
      refine Completion.denseRange_coe.induction_on y ?_ ?_
      · exact isClosed_eq (continuous_const.inner (U.rotation s).continuous)
          (continuous_const.inner continuous_id)
      · exact hpf z
  apply ext_inner_right ℂ
  intro y
  have hy : U.rotation s (U.rotation (-s) y)=y := by
    change (U.rotation s*U.rotation (-s)) y=y
    rw [← U.rotation_add,add_neg_cancel,U.rotation_zero,one_apply_eq_self]
  rw [← hy]
  change inner ℂ (U.stressPropagator hc f 1 x) (U.rotation s (U.rotation (-s) y))=_
  rw [hall,U.rotation_inner]
lemma mobiusRepresentation_rotation (hc : A.toVertexAlgebra.C2Cofinite) (s : ℝ) (x : Completion V) :
    U.mobiusRepresentation hc (QuotientGroup.mk (CircleMobiusGeometry.rotation s)) x=U.rotation s x := by
  change U.mobiusLiftUnitary hc (CircleMobiusGeometry.rotation s) x=_
  rw [U.mobiusLiftUnitary_apply]
  have hphase : U.mobiusVacuumPhase hc (CircleMobiusGeometry.rotation s)=1 := by
    dsimp only [mobiusVacuumPhase,CircleMobiusGeometry.rotation]
    rw [U.diffeomorphismImplementer_rotation,U.rotation_vacuum,inner_self_eq_norm_sq_to_K,
      U.completion_vacuum_norm]
    simp
  rw [hphase,inv_one,one_smul]
  exact U.diffeomorphismImplementer_rotation hc s x
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ConformalNetContinuation
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

def conformalNetStructure (hc : A.toVertexAlgebra.C2Cofinite) :
    IrreducibleConformalNetStructure (U.intervalAlgebra hc) where
  separable := U.hilbertCompletion_separable
  carrier_congr := by
    intro I J h
    exact congrArg (U.localAlgebra hc) h
  isotony := by
    intro I J h
    exact U.localAlgebra_isotone hc h
  locality := by
    intro I J h
    exact U.localAlgebra_locality hc I.isOpen_carrier J.isOpen_carrier h
  mobius := (U.mobiusRepresentation hc).comp CircleMobiusGeometry.projectiveStandardAction
  mobius_continuous := (U.mobiusRepresentation_continuous hc).comp CircleMobiusGeometry.projectiveStandardAction_continuous
  diffeomorphism := U.diffeomorphismProjectiveRepresentation hc
  diffeomorphism_continuous := U.diffeomorphismProjectiveRepresentation_continuous hc
  extends_mobius := fun F => (U.mobiusRepresentation_projective hc (CircleMobiusGeometry.projectiveStandardAction F)).symm
  covariance := by
    intro F
    induction F using QuotientGroup.induction_on with
    | H F =>
      intro I J h B
      change (U.diffeomorphismImplementer hc F).conjStarAlgEquiv B ∈
        U.localAlgebra hc J.carrier ↔ B ∈ U.localAlgebra hc I.carrier
      change J.carrier=F.onCircle '' I.carrier at h
      rw [h]
      exact U.localAlgebra_diffeomorphism_iff hc F I.isOpen_carrier B
  local_action := by
    intro F
    induction F using QuotientGroup.induction_on with
    | H F =>
      intro I h B hB
      exact U.diffeomorphism_local_action hc F I h hB
  vacuum := (A.vacuum:Completion V)
  vacuum_norm := U.completion_vacuum_norm
  vacuum_invariant := fun F => U.mobiusRepresentation_vacuum hc _
  vacuum_unique := by
    intro x hx
    apply U.rotation_fixed_scalar
    intro t
    rw [← U.mobiusRepresentation_rotation hc t]
    simpa only [MonoidHom.comp_apply,CircleMobiusGeometry.projectiveStandardAction_rotation] using
      hx (QuotientGroup.mk (CircleMobiusGeometry.rotationMatrix t))
  vacuum_cyclic := U.interval_vacuum_cyclic hc
  hamiltonian := U.conformalHamiltonian
  hamiltonian_selfAdjoint := U.energyOperator_selfAdjoint (fun d => d)
  positive_energy := fun _ _ h => U.conformalHamiltonian_nonnegative h
  rotation_flow := by
    intro t
    apply ContinuousLinearMap.ext
    intro x
    change U.mobiusRepresentation hc
      (CircleMobiusGeometry.projectiveStandardAction (QuotientGroup.mk (CircleMobiusGeometry.rotationMatrix t))) x=_
    rw [CircleMobiusGeometry.projectiveStandardAction_rotation]
    rw [U.mobiusRepresentation_rotation,U.rotation_eq_hamiltonianFlow]
  irreducible := by
    intro Q hQ
    exact U.interval_commutant_scalar hc hQ


end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end


