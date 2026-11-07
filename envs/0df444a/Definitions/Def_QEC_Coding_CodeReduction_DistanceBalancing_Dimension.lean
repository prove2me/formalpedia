-- Prove2me | Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
-- name    : QEC_Coding_CodeReduction_DistanceBalancing_Dimension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:20:47.077963+00:00
-- url     : https://prove2.me/theorems/576a5d29-453e-4f6b-9d24-2f9912468e44
-- title:
--   Dimension
-- statement:
--   Definitions and structural lemmas for Dimension, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Dimension.lean

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_DistanceBalancing_boundary1_apply_inr
import Theorems.Thm_QEC_Coding_DistanceBalancing_boundary2_apply_inl
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding.DistanceBalancing
universe u
open scoped TensorProduct
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
abbrev ClassicalKernel := LinearMap.ker (Matrix.toLin' D.classicalBoundary)
noncomputable def sourceCycleSection :
    (sourceChainComplex D).middleHomology →ₗ[ZMod 2]
      (sourceChainComplex D).middleCycleCode.carrier :=
  Classical.choose
    ((sourceChainComplex D).middleBoundaryInCycles.mkQ
      |>.exists_rightInverse_of_surjective
        (LinearMap.range_eq_top.mpr
          (Submodule.mkQ_surjective
            (sourceChainComplex D).middleBoundaryInCycles)))
noncomputable def pureTensorWord
    (h : (sourceChainComplex D).middleHomology)
    (w : ClassicalKernel D) :
    Word (ZMod 2) (QubitIndex xOne xTwo classicalBit classicalCheck) :=
  Sum.elim
    (fun p => (sourceCycleSection D h).1 p.1 * w.1 p.2)
    (fun _ => 0)
theorem pureTensorWord_mem_middleCycleCode
    (h : (sourceChainComplex D).middleHomology)
    (w : ClassicalKernel D) :
    pureTensorWord D h w ∈ (chainComplex D).middleCycleCode.carrier := by
  rw [(chainComplex D).mem_middleCycleCode_iff]
  ext q
  cases q with
  | inl q =>
      rcases q with ⟨x0, a⟩
      simp only [Pi.zero_apply]
      change boundary1 D (pureTensorWord D h w) (Sum.inl (x0, a)) = 0
      rw [boundary1_apply_inl]
      have hCycle := (sourceCycleSection D h).2
      have hZero := ((sourceChainComplex D).mem_middleCycleCode_iff
        (sourceCycleSection D h).1).mp hCycle
      change Matrix.toLin' D.xBoundary1 (sourceCycleSection D h).1 = 0 at hZero
      have hAt := congrFun hZero x0
      change
        (∑ x1 : xOne,
          D.xBoundary1 x0 x1 * (sourceCycleSection D h).1 x1) = 0 at hAt
      have hAt' :
          (∑ x1 : xOne,
            D.xBoundary1 x0 x1 * (sourceCycleSection D h).1 x1) = 0 := by
        exact hAt
      simp only [xOneBitSlice, pureTensorWord, Sum.elim_inl]
      calc
        (∑ x1 : xOne,
            D.xBoundary1 x0 x1 *
              ((sourceCycleSection D h).1 x1 * w.1 a)) =
            (∑ x1 : xOne,
              D.xBoundary1 x0 x1 * (sourceCycleSection D h).1 x1) *
                w.1 a := by
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro x1 _
                  rw [mul_assoc]
        _ = 0 := by rw [hAt', zero_mul]
  | inr q =>
      rcases q with ⟨x1, b⟩
      simp only [Pi.zero_apply]
      change boundary1 D (pureTensorWord D h w) (Sum.inr (x1, b)) = 0
      rw [boundary1_apply_inr]
      have hKernel := LinearMap.mem_ker.mp w.2
      have hAt := congrFun hKernel b
      change
        (∑ a : classicalBit, D.classicalBoundary b a * w.1 a) = 0 at hAt
      have hAt' :
          (∑ a : classicalBit, D.classicalBoundary b a * w.1 a) = 0 := by
        exact hAt
      simp only [pureTensorWord, xOneBitSlice, Sum.elim_inl,
        xTwoCheckSlice, Sum.elim_inr, mul_zero, Finset.sum_const_zero,
        add_zero]
      calc
        (∑ a : classicalBit,
            D.classicalBoundary b a *
              ((sourceCycleSection D h).1 x1 * w.1 a)) =
            (sourceCycleSection D h).1 x1 *
              (∑ a : classicalBit, D.classicalBoundary b a * w.1 a) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro a _
                ring
        _ = 0 := by rw [hAt', mul_zero]
noncomputable def pureTensorCycle
    (h : (sourceChainComplex D).middleHomology)
    (w : ClassicalKernel D) :
    (chainComplex D).middleCycleCode.carrier :=
  ⟨pureTensorWord D h w, pureTensorWord_mem_middleCycleCode D h w⟩
noncomputable def pureTensorCycleBilinear :
    (sourceChainComplex D).middleHomology →ₗ[ZMod 2]
      ClassicalKernel D →ₗ[ZMod 2]
        (chainComplex D).middleCycleCode.carrier where
  toFun h :=
    { toFun := pureTensorCycle D h
      map_add' := by
        intro w₁ w₂
        apply Subtype.ext
        ext q
        cases q <;> simp [pureTensorCycle, pureTensorWord] <;> ring
      map_smul' := by
        intro c w
        apply Subtype.ext
        ext q
        cases q <;> simp [pureTensorCycle, pureTensorWord] <;> ring }
  map_add' := by
    intro h₁ h₂
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    ext q
    cases q <;> simp [pureTensorCycle, pureTensorWord] <;> ring
  map_smul' := by
    intro c h
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    ext q
    cases q <;> simp [pureTensorCycle, pureTensorWord] <;> ring
noncomputable def tensorCycleMap :
    (sourceChainComplex D).middleHomology ⊗[ZMod 2] ClassicalKernel D →ₗ[ZMod 2]
      (chainComplex D).middleCycleCode.carrier :=
  TensorProduct.lift (pureTensorCycleBilinear D)
@[simp]
theorem tensorCycleMap_tmul
    (h : (sourceChainComplex D).middleHomology)
    (w : ClassicalKernel D) :
    tensorCycleMap D (h ⊗ₜ[ZMod 2] w) = pureTensorCycle D h w := by
  rfl
noncomputable def tensorHomologyMap :
    (sourceChainComplex D).middleHomology ⊗[ZMod 2] ClassicalKernel D →ₗ[ZMod 2]
      (chainComplex D).middleHomology :=
  (chainComplex D).middleBoundaryInCycles.mkQ.comp (tensorCycleMap D)
@[simp]
theorem tensorHomologyMap_tmul
    (h : (sourceChainComplex D).middleHomology)
    (w : ClassicalKernel D) :
    tensorHomologyMap D (h ⊗ₜ[ZMod 2] w) =
      (chainComplex D).middleBoundaryInCycles.mkQ
        (pureTensorCycle D h w) := by
  rfl
noncomputable def cycleToHomologySlices :
    (chainComplex D).middleCycleCode.carrier →ₗ[ZMod 2]
      classicalBit → (sourceChainComplex D).middleHomology where
  toFun z := fun a =>
    (sourceChainComplex D).middleBoundaryInCycles.mkQ
      ⟨xOneBitSlice z.1 a, xOneBitSlice_mem_middleCycleCode D z.1 z.2 a⟩
  map_add' z₁ z₂ := by
    funext a
    change (sourceChainComplex D).middleBoundaryInCycles.mkQ
        ⟨xOneBitSlice (z₁.1 + z₂.1) a, _⟩ =
      (sourceChainComplex D).middleBoundaryInCycles.mkQ
          ⟨xOneBitSlice z₁.1 a, _⟩ +
        (sourceChainComplex D).middleBoundaryInCycles.mkQ
          ⟨xOneBitSlice z₂.1 a, _⟩
    rw [← (sourceChainComplex D).middleBoundaryInCycles.mkQ.map_add]
    congr 1
  map_smul' c z := by
    funext a
    change (sourceChainComplex D).middleBoundaryInCycles.mkQ
        ⟨xOneBitSlice (c • z.1) a, _⟩ =
      c • (sourceChainComplex D).middleBoundaryInCycles.mkQ
        ⟨xOneBitSlice z.1 a, _⟩
    rw [← (sourceChainComplex D).middleBoundaryInCycles.mkQ.map_smul]
    congr 1
theorem middleBoundaryInCycles_le_ker_cycleToHomologySlices :
    (chainComplex D).middleBoundaryInCycles ≤
      LinearMap.ker (cycleToHomologySlices D) := by
  intro z hz
  apply LinearMap.mem_ker.mpr
  funext a
  apply (Submodule.Quotient.mk_eq_zero
    (sourceChainComplex D).middleBoundaryInCycles).mpr
  change xOneBitSlice z.1 a ∈
    (sourceChainComplex D).middleBoundaryCode.carrier
  rcases ((chainComplex D).mem_middleBoundaryCode_iff z.1).mp hz with
    ⟨c, hc⟩
  apply ((sourceChainComplex D).mem_middleBoundaryCode_iff _).mpr
  refine ⟨xTwoBitSlice c a, ?_⟩
  ext x1
  change
    (∑ x2 : xTwo, D.xBoundary2 x1 x2 * xTwoBitSlice c a x2) =
      z.1 (Sum.inl (x1, a))
  calc
    _ = boundary2 D c (Sum.inl (x1, a)) :=
      (boundary2_apply_inl D c x1 a).symm
    _ = z.1 (Sum.inl (x1, a)) := congrFun hc _
noncomputable def homologySliceMap :
    (chainComplex D).middleHomology →ₗ[ZMod 2]
      classicalBit → (sourceChainComplex D).middleHomology :=
  (chainComplex D).middleBoundaryInCycles.liftQ
    (cycleToHomologySlices D)
    (middleBoundaryInCycles_le_ker_cycleToHomologySlices D)
noncomputable def kernelTensorToSlices :
    (sourceChainComplex D).middleHomology ⊗[ZMod 2] ClassicalKernel D →ₗ[ZMod 2]
      classicalBit → (sourceChainComplex D).middleHomology :=
  (TensorProduct.piScalarRight (ZMod 2) (ZMod 2)
      (sourceChainComplex D).middleHomology classicalBit).toLinearMap.comp
    ((ClassicalKernel D).subtype.lTensor
      (sourceChainComplex D).middleHomology)
end QEC.Coding.DistanceBalancing


