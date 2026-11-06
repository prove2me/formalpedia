-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationKernel
-- name    : QEC_Coding_AlgebraicGeometry_Codes_EvaluationKernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:30:01.416011+00:00
-- url     : https://prove2.me/theorems/989a97b1-7f25-4090-87cc-75e7672e3afe
-- title:
--   Evaluation Kernel
-- statement:
--   Definitions and structural lemmas for Evaluation Kernel, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/EvaluationKernel.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_riemannRochSubmodule_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochSubmodule_mono
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluateRegular_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluationLinearMap_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationZero_mem_riemannRochSubmodule_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_zeroCoordinateDivisor_apply_at
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap_apply
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped BigOperators
noncomputable section
variable {k F ι : Type*} [Field k] [Finite k] [Field F] [Algebra k F] [Fintype ι]
theorem zeroCoordinateDivisor_nonnegative (Q : ι → RationalPlace k F) (S : Finset ι) :
    0 ≤ zeroCoordinateDivisor Q S := by
  classical
  intro P
  change 0 ≤ zeroCoordinateDivisor Q S P
  unfold zeroCoordinateDivisor
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_nonneg
  intro j _
  simp only [Finsupp.single_apply]
  split_ifs <;> norm_num
theorem evaluationZeroOn_of_mem_riemannRochSubmodule_sub
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (S : Finset ι)
    (f : GlobalPlace.riemannRochSubmodule G)
    (hf : (f : F) ∈ GlobalPlace.riemannRochSubmodule (G - zeroCoordinateDivisor Q S)) :
    ∀ j ∈ S, agEvaluationLinearMap G Q hG f j = 0 := by
  intro j hj
  rw [agEvaluationLinearMap_apply, (Q j).evaluateRegular_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  change (Q j).place.valuation (f : F) < 1
  have hb := (GlobalPlace.mem_riemannRochSubmodule_iff _ _).mp hf (Q j).place
  rw [Finsupp.sub_apply, hG j, zeroCoordinateDivisor_apply_at Q hQ S hj] at hb
  apply lt_of_le_of_lt hb
  simpa only [WithZero.exp_zero] using
    (WithZero.exp_lt_exp.mpr (by norm_num : (0 : ℤ) - 1 < 0))
def agEvaluationKernelEquiv
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) :
    (agEvaluationLinearMap G Q hG).ker ≃ₗ[k]
      GlobalPlace.riemannRochSubmodule (G - evaluationDivisor Q) where
  toFun f := ⟨(f.val : F), evaluationZero_mem_riemannRochSubmodule_sub G Q hQ hG
    f.val (LinearMap.mem_ker.mp f.property)⟩
  invFun f := by
    let fG : GlobalPlace.riemannRochSubmodule G :=
      ⟨(f : F), GlobalPlace.riemannRochSubmodule_mono
        (sub_le_self G (zeroCoordinateDivisor_nonnegative Q Finset.univ)) f.property⟩
    refine ⟨fG, LinearMap.mem_ker.mpr ?_⟩
    ext j
    exact evaluationZeroOn_of_mem_riemannRochSubmodule_sub G Q hQ hG Finset.univ
      fG f.property j (Finset.mem_univ j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end
end QEC.Coding.AlgebraicGeometry


