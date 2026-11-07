-- Prove2me | Definitions.Def_QEC_Coding_CSS_SubsystemDual
-- name    : QEC_Coding_CSS_SubsystemDual
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:37:02.73951+00:00
-- url     : https://prove2.me/theorems/dc2499ac-d81e-476c-8455-77dbe52d40b5
-- title:
--   Subsystem Dual
-- statement:
--   Definitions and structural lemmas for Subsystem Dual, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/SubsystemDual.lean

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_Coding_wordLinearMapTranspose_transpose
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding.SubsystemCSSData
universe u v
variable {i0 i1 i2 : Type u} {LogicalZ LogicalX : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]
variable [AddCommGroup LogicalZ] [Module (ZMod 2) LogicalZ]
variable [AddCommGroup LogicalX] [Module (ZMod 2) LogicalX]
variable [Module.Finite (ZMod 2) LogicalZ]
variable [Module.Finite (ZMod 2) LogicalX]
noncomputable def dualCocycleToOriginalHomology
    (K : ChainComplexData (ZMod 2)
      (Word (ZMod 2) i0) (Word (ZMod 2) i1) (Word (ZMod 2) i2)) :
    (dualChainComplex K).middleCocycleCode.carrier →ₗ[ZMod 2]
      K.middleHomology where
  toFun x := K.middleBoundaryInCycles.mkQ
    ⟨x.1, by
      rw [K.mem_middleCycleCode_iff]
      have hx := ((dualChainComplex K).mem_middleCocycleCode_iff x.1).mp x.2
      simpa only [dualChainComplex_boundary2,
        wordLinearMapTranspose_transpose] using hx⟩
  map_add' x y := by
    change K.middleBoundaryInCycles.mkQ ⟨x.1 + y.1, _⟩ =
      K.middleBoundaryInCycles.mkQ ⟨x.1, _⟩ +
        K.middleBoundaryInCycles.mkQ ⟨y.1, _⟩
    rw [← map_add]
    rfl
  map_smul' c x := by
    change K.middleBoundaryInCycles.mkQ ⟨c • x.1, _⟩ =
      c • K.middleBoundaryInCycles.mkQ ⟨x.1, _⟩
    rw [← map_smul]
    rfl
theorem dual_middleCoboundary_le_ker_dualCocycleToOriginalHomology
    (K : ChainComplexData (ZMod 2)
      (Word (ZMod 2) i0) (Word (ZMod 2) i1) (Word (ZMod 2) i2)) :
    (dualChainComplex K).middleCoboundaryInCocycles ≤
      LinearMap.ker (dualCocycleToOriginalHomology K) := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  change K.middleBoundaryInCycles.mkQ ⟨x.1, _⟩ = 0
  apply (Submodule.Quotient.mk_eq_zero K.middleBoundaryInCycles).mpr
  change x.1 ∈ K.middleBoundaryCode.carrier
  change x.1 ∈ (dualChainComplex K).firstCoboundaryCheckCode.carrier at hx
  rcases ((dualChainComplex K).mem_firstCoboundaryCheckCode_iff x.1).mp hx with
    ⟨w, hw⟩
  apply (K.mem_middleBoundaryCode_iff x.1).mpr
  refine ⟨w, ?_⟩
  simpa only [dualChainComplex_boundary1,
    wordLinearMapTranspose_transpose] using hw
noncomputable def dualCohomologyToOriginalHomology
    (K : ChainComplexData (ZMod 2)
      (Word (ZMod 2) i0) (Word (ZMod 2) i1) (Word (ZMod 2) i2)) :
    (dualChainComplex K).middleCohomology →ₗ[ZMod 2] K.middleHomology :=
  (dualChainComplex K).middleCoboundaryInCocycles.liftQ
    (dualCocycleToOriginalHomology K)
    (dual_middleCoboundary_le_ker_dualCocycleToOriginalHomology K)
@[simp]
theorem dualCohomologyToOriginalHomology_mk
    (K : ChainComplexData (ZMod 2)
      (Word (ZMod 2) i0) (Word (ZMod 2) i1) (Word (ZMod 2) i2))
    (x : (dualChainComplex K).middleCocycleCode.carrier) :
    dualCohomologyToOriginalHomology K
        ((dualChainComplex K).middleCoboundaryInCocycles.mkQ x) =
      K.middleBoundaryInCycles.mkQ
        ⟨x.1, by
          rw [K.mem_middleCycleCode_iff]
          have hx := ((dualChainComplex K).mem_middleCocycleCode_iff x.1).mp x.2
          simpa only [dualChainComplex_boundary2,
            wordLinearMapTranspose_transpose] using hx⟩ := rfl
theorem dualCohomologyToOriginalHomology_surjective
    (K : ChainComplexData (ZMod 2)
      (Word (ZMod 2) i0) (Word (ZMod 2) i1) (Word (ZMod 2) i2)) :
    Function.Surjective (dualCohomologyToOriginalHomology K) := by
  intro h
  obtain ⟨x, rfl⟩ := K.middleBoundaryInCycles.mkQ_surjective h
  let xd : (dualChainComplex K).middleCocycleCode.carrier :=
    ⟨x.1, by
      rw [(dualChainComplex K).mem_middleCocycleCode_iff]
      simpa only [dualChainComplex_boundary2,
        wordLinearMapTranspose_transpose] using
          (K.mem_middleCycleCode_iff x.1).mp x.2⟩
  exact ⟨(dualChainComplex K).middleCoboundaryInCocycles.mkQ xd, by
    rw [dualCohomologyToOriginalHomology_mk]⟩
noncomputable def dual
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) :
    SubsystemCSSData i2 i1 i0 LogicalX LogicalZ where
  complex := dualChainComplex D.complex
  homologyProjection := D.cohomologyProjection
  cohomologyProjection := D.homologyProjection.comp
    (dualCohomologyToOriginalHomology D.complex)
  homologyProjection_surjective := D.cohomologyProjection_surjective
  cohomologyProjection_surjective :=
    D.homologyProjection_surjective.comp
      (dualCohomologyToOriginalHomology_surjective D.complex)
  logical_finrank_eq := D.logical_finrank_eq.symm
end QEC.Coding.SubsystemCSSData


