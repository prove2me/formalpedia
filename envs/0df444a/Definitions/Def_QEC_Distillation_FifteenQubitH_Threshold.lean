-- Prove2me | Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
-- name    : QEC_Distillation_FifteenQubitH_Threshold
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T04:23:23.004255+00:00
-- url     : https://prove2.me/theorems/5b560466-66ea-4fb3-9929-49472a6c8c4d
-- title:
--   Threshold
-- statement:
--   Definitions and structural lemmas for Threshold, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_acceptedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_operation
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_rejectedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_resourceCount
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_successProbability
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hResourceTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceHDensity_toOperator
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_acceptedOutput
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_operation
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_rejectedOutput
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_resourceCount
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_successProbability
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.OneQubitMagic.hResourceTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.sourceHDensity_toOperator
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace BK15
namespace Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic
def bk15Bias (epsilon : Real) : Real := 1 - 2 * epsilon
def bk15Recurrence (epsilon : Real) : Real :=
  (1 - 15 * bk15Bias epsilon ^ 7 + 15 * bk15Bias epsilon ^ 8 -
    bk15Bias epsilon ^ 15) /
    (2 * (1 + 15 * bk15Bias epsilon ^ 8))
def bk15FixedPolynomial (bias : Real) : Real :=
  bias ^ 14 - 15 * bias ^ 8 + 15 * bias ^ 6 - 1
def bk15FixedCubic (y : Real) : Real := y ^ 3 - 5 * y ^ 2 + 6 * y - 16
theorem bk15Recurrence_denominator_pos (epsilon : Real) :
    0 < 1 + 15 * bk15Bias epsilon ^ 8 := by
  have hpow : 0 <= bk15Bias epsilon ^ 8 := by positivity
  nlinarith
theorem bk15Recurrence_scaled_denominator_pos (epsilon : Real) :
    0 < 2 * (1 + 15 * bk15Bias epsilon ^ 8) := by
  nlinarith [bk15Recurrence_denominator_pos epsilon]
theorem bk15FixedPolynomial_cubic_factor (bias : Real) (hbias : bias ≠ 0) :
    bk15FixedPolynomial bias / bias ^ 7 =
      (bias - bias⁻¹) *
        bk15FixedCubic ((bias + bias⁻¹) ^ 2) := by
  unfold bk15FixedPolynomial bk15FixedCubic
  field_simp [hbias]
  ring
theorem bk15FixedCubic_strictMonoOn :
    StrictMonoOn bk15FixedCubic (Set.Ici 4) := by
  intro x hx y hy hxy
  have hx' : 4 <= x := hx
  have hy' : 4 <= y := hy
  have hfactor :
      bk15FixedCubic y - bk15FixedCubic x =
        (y - x) * (y ^ 2 + x * y + x ^ 2 - 5 * (x + y) + 6) := by
    unfold bk15FixedCubic
    ring
  have hcoefficient : 0 < y ^ 2 + x * y + x ^ 2 - 5 * (x + y) + 6 := by
    have hshift : y ^ 2 + x * y + x ^ 2 - 5 * (x + y) + 6 =
        14 + 7 * (x - 4) + 7 * (y - 4) +
          (x - 4) ^ 2 + (x - 4) * (y - 4) + (y - 4) ^ 2 := by
      ring
    rw [hshift]
    have hxnonneg : 0 <= x - 4 := sub_nonneg.mpr hx'
    have hynonneg : 0 <= y - 4 := sub_nonneg.mpr hy'
    positivity
  nlinarith [hfactor, mul_pos (sub_pos.mpr hxy) hcoefficient]
theorem bias_add_inv_ge_two {bias : Real} (hpositive : 0 < bias) :
    2 <= bias + bias⁻¹ := by
  have hidentity : bias + bias⁻¹ - 2 = (bias - 1) ^ 2 / bias := by
    field_simp [hpositive.ne']
    ring
  have hnonneg : 0 <= (bias - 1) ^ 2 / bias := by positivity
  linarith
theorem bias_cubic_argument_mem_Ici_four
    {bias : Real} (hpositive : 0 < bias) :
    (bias + bias⁻¹) ^ 2 ∈ Set.Ici (4 : Real) := by
  have hsum := bias_add_inv_ge_two hpositive
  let x : Real := bias + bias⁻¹
  have hsum' : 2 <= x := by simpa [x] using hsum
  change 4 <= x ^ 2
  have hproduct : 0 <=
      (x - 2) * (x + 2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith
theorem bias_sub_inv_neg {bias : Real}
    (hpositive : 0 < bias) (hlt_one : bias < 1) :
    bias - bias⁻¹ < 0 := by
  have hidentity : bias - bias⁻¹ = (bias ^ 2 - 1) / bias := by
    field_simp [hpositive.ne']
  have hsq_lt : bias ^ 2 < 1 := by
    have hmul : 0 < bias * (1 - bias) := mul_pos hpositive (sub_pos.mpr hlt_one)
    nlinarith
  rw [hidentity]
  exact div_neg_of_neg_of_pos (by linarith) hpositive
theorem cubic_eq_zero_of_fixedPolynomial_root
    {bias : Real} (hpositive : 0 < bias) (hlt_one : bias < 1)
    (hroot : bk15FixedPolynomial bias = 0) :
    bk15FixedCubic ((bias + bias⁻¹) ^ 2) = 0 := by
  have hfactor := bk15FixedPolynomial_cubic_factor bias hpositive.ne'
  rw [hroot] at hfactor
  norm_num at hfactor
  exact hfactor.resolve_left
    (ne_of_lt (bias_sub_inv_neg hpositive hlt_one))
theorem fixedPolynomial_root_unique_in_unitInterval
    {left right : Real} (hleft : 0 < left) (hleft_one : left < 1)
    (hright : 0 < right) (hright_one : right < 1)
    (hleft_root : bk15FixedPolynomial left = 0)
    (hright_root : bk15FixedPolynomial right = 0) :
    left = right := by
  have hleft_cubic :=
    cubic_eq_zero_of_fixedPolynomial_root hleft hleft_one hleft_root
  have hright_cubic :=
    cubic_eq_zero_of_fixedPolynomial_root hright hright_one hright_root
  have hleft_mem := bias_cubic_argument_mem_Ici_four hleft
  have hright_mem := bias_cubic_argument_mem_Ici_four hright
  have hargument : (left + left⁻¹) ^ 2 = (right + right⁻¹) ^ 2 := by
    apply (bk15FixedCubic_strictMonoOn.eq_iff_eq hleft_mem hright_mem).mp
    rw [hleft_cubic, hright_cubic]
  have hleft_sum_pos : 0 < left + left⁻¹ := by positivity
  have hright_sum_pos : 0 < right + right⁻¹ := by positivity
  have hsum : left + left⁻¹ = right + right⁻¹ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hargument with h | h
    · exact h
    · exfalso
      rw [h] at hleft_sum_pos
      linarith
  have hproduct : (left - right) * (left * right - 1) = 0 := by
    calc
      (left - right) * (left * right - 1) =
          left * right * ((left + left⁻¹) - (right + right⁻¹)) := by
            field_simp [hleft.ne', hright.ne']
            ring
      _ = 0 := by rw [hsum]; ring
  rcases mul_eq_zero.mp hproduct with heq | hunit
  · exact sub_eq_zero.mp heq
  · exfalso
    have hproduct_lt : left * right < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left hleft.le hleft_one hright_one.le
    nlinarith
def bk15BiasUpper : Real := 35851 / 50000
def bk15BiasLower : Real := 35853 / 50000
theorem bk15BiasUpper_lt_lower : bk15BiasUpper < bk15BiasLower := by
  norm_num [bk15BiasUpper, bk15BiasLower]
theorem bk15FixedPolynomial_upper_neg : bk15FixedPolynomial bk15BiasUpper < 0 := by
  norm_num [bk15FixedPolynomial, bk15BiasUpper]
theorem bk15FixedPolynomial_lower_pos : 0 < bk15FixedPolynomial bk15BiasLower := by
  norm_num [bk15FixedPolynomial, bk15BiasLower]
theorem exists_interior_bias_fixedPolynomial_root :
    ∃ bias, bk15BiasUpper < bias ∧ bias < bk15BiasLower ∧
      bk15FixedPolynomial bias = 0 := by
  have hcontinuous : Continuous bk15FixedPolynomial := by
    unfold bk15FixedPolynomial
    fun_prop
  have himage := intermediate_value_Icc bk15BiasUpper_lt_lower.le
    hcontinuous.continuousOn
      ⟨bk15FixedPolynomial_upper_neg.le,
        bk15FixedPolynomial_lower_pos.le⟩
  rcases himage with ⟨bias, hbias_mem, hbias_root⟩
  refine ⟨bias, ?_, ?_, hbias_root⟩
  · rcases hbias_mem with ⟨hupper, hlower⟩
    exact lt_of_le_of_ne hupper (by
      intro heq
      rw [← heq] at hbias_root
      linarith [bk15FixedPolynomial_upper_neg])
  · rcases hbias_mem with ⟨hupper, hlower⟩
    exact lt_of_le_of_ne hlower (by
      intro heq
      rw [heq] at hbias_root
      linarith [bk15FixedPolynomial_lower_pos])
theorem existsUnique_interior_bias_fixedPolynomial_root :
    ∃! bias, 0 < bias ∧ bias < 1 ∧ bk15FixedPolynomial bias = 0 := by
  rcases exists_interior_bias_fixedPolynomial_root with
    ⟨bias, hupper, hlower, hroot⟩
  refine ⟨bias, ?_, ?_⟩
  · refine ⟨?_, ?_, hroot⟩
    · have : 0 < bk15BiasUpper := by norm_num [bk15BiasUpper]
      linarith
    · have : bk15BiasLower < 1 := by norm_num [bk15BiasLower]
      linarith
  · intro other hother
    have hbias_pos : 0 < bias := by
      have hendpoint : 0 < bk15BiasUpper := by
        norm_num [bk15BiasUpper]
      linarith
    have hbias_one : bias < 1 := by
      have hendpoint : bk15BiasLower < 1 := by
        norm_num [bk15BiasLower]
      linarith
    exact fixedPolynomial_root_unique_in_unitInterval
      (by exact hother.1) (by exact hother.2.1)
      hbias_pos hbias_one
      hother.2.2 hroot
noncomputable def bk15BiasStar : Real :=
  Classical.choose existsUnique_interior_bias_fixedPolynomial_root
theorem bk15BiasStar_pos : 0 < bk15BiasStar :=
  (Classical.choose_spec existsUnique_interior_bias_fixedPolynomial_root).1.1
theorem bk15BiasStar_lt_one : bk15BiasStar < 1 :=
  (Classical.choose_spec existsUnique_interior_bias_fixedPolynomial_root).1.2.1
theorem bk15FixedPolynomial_biasStar :
    bk15FixedPolynomial bk15BiasStar = 0 :=
  (Classical.choose_spec existsUnique_interior_bias_fixedPolynomial_root).1.2.2
noncomputable def epsilonStar : Real := (1 - bk15BiasStar) / 2
theorem bk15Bias_epsilonStar : bk15Bias epsilonStar = bk15BiasStar := by
  unfold bk15Bias epsilonStar
  ring
theorem epsilonStar_lt_half : epsilonStar < 1 / 2 := by
  unfold epsilonStar
  linarith [bk15BiasStar_pos]
theorem bk15Recurrence_sub_input (epsilon : Real) :
    bk15Recurrence epsilon - epsilon =
      -(bk15Bias epsilon * bk15FixedPolynomial (bk15Bias epsilon)) /
        (2 * (1 + 15 * bk15Bias epsilon ^ 8)) := by
  have hdenom : 1 + 15 * bk15Bias epsilon ^ 8 ≠ 0 :=
    (bk15Recurrence_denominator_pos epsilon).ne'
  unfold bk15Recurrence bk15FixedPolynomial bk15Bias
  field_simp [hdenom]
  ring
theorem bias_add_inv_strictAnti_of_lt
    {smaller larger : Real}
    (hsmaller_pos : 0 < smaller) (hsmaller_one : smaller < 1)
    (hlarger_pos : 0 < larger) (hlarger_one : larger < 1)
    (hlt : smaller < larger) :
    larger + larger⁻¹ < smaller + smaller⁻¹ := by
  have hidentity :
      larger * smaller * ((larger + larger⁻¹) - (smaller + smaller⁻¹)) =
        (larger - smaller) * (larger * smaller - 1) := by
    field_simp [hsmaller_pos.ne', hlarger_pos.ne']
    ring
  have hproduct_lt : larger * smaller < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hlarger_pos.le hlarger_one hsmaller_one.le
  have hright_neg : (larger - smaller) * (larger * smaller - 1) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hlt) (by linarith)
  have hleft_neg :
      larger * smaller * ((larger + larger⁻¹) - (smaller + smaller⁻¹)) < 0 := by
    rw [hidentity]
    exact hright_neg
  exact sub_neg.mp <|
    neg_of_mul_neg_right hleft_neg (mul_pos hlarger_pos hsmaller_pos).le
theorem fixedPolynomial_pos_of_biasStar_lt
    {bias : Real} (hstar_lt : bk15BiasStar < bias) (hbias_one : bias < 1) :
    0 < bk15FixedPolynomial bias := by
  have hbias_pos : 0 < bias := bk15BiasStar_pos.trans hstar_lt
  have hsum_lt :
      bias + bias⁻¹ < bk15BiasStar + bk15BiasStar⁻¹ :=
    bias_add_inv_strictAnti_of_lt
      bk15BiasStar_pos bk15BiasStar_lt_one hbias_pos hbias_one hstar_lt
  have hbias_sum_pos : 0 < bias + bias⁻¹ := by positivity
  have hstar_sum_pos : 0 < bk15BiasStar + bk15BiasStar⁻¹ := by
    exact add_pos bk15BiasStar_pos (inv_pos.mpr bk15BiasStar_pos)
  have hargument_lt :
      (bias + bias⁻¹) ^ 2 < (bk15BiasStar + bk15BiasStar⁻¹) ^ 2 :=
    (sq_lt_sq₀ hbias_sum_pos.le hstar_sum_pos.le).mpr hsum_lt
  have hbias_mem := bias_cubic_argument_mem_Ici_four hbias_pos
  have hstar_mem := bias_cubic_argument_mem_Ici_four bk15BiasStar_pos
  have hcubic_lt := bk15FixedCubic_strictMonoOn hbias_mem hstar_mem hargument_lt
  have hstar_cubic := cubic_eq_zero_of_fixedPolynomial_root
    bk15BiasStar_pos bk15BiasStar_lt_one bk15FixedPolynomial_biasStar
  have hcubic_neg : bk15FixedCubic ((bias + bias⁻¹) ^ 2) < 0 := by
    rw [hstar_cubic] at hcubic_lt
    exact hcubic_lt
  have hfactor := bk15FixedPolynomial_cubic_factor bias hbias_pos.ne'
  have hdiv_pos : 0 < bk15FixedPolynomial bias / bias ^ 7 := by
    rw [hfactor]
    exact mul_pos_of_neg_of_neg (bias_sub_inv_neg hbias_pos hbias_one) hcubic_neg
  exact (div_pos_iff_of_pos_right (pow_pos hbias_pos _)).mp hdiv_pos
theorem bk15Recurrence_numerator_weight_sum (epsilon : Real) :
    1 - 15 * bk15Bias epsilon ^ 7 + 15 * bk15Bias epsilon ^ 8 -
        bk15Bias epsilon ^ 15 =
      32 *
        (35 * (epsilon ^ 3 * (1 - epsilon) ^ 12) +
          168 * (epsilon ^ 5 * (1 - epsilon) ^ 10) +
          435 * (epsilon ^ 7 * (1 - epsilon) ^ 8) +
          280 * (epsilon ^ 9 * (1 - epsilon) ^ 6) +
          105 * (epsilon ^ 11 * (1 - epsilon) ^ 4) + epsilon ^ 15) := by
  unfold bk15Bias
  ring
theorem bk15Recurrence_pos_of_pos_lt_epsilonStar
    {epsilon : Real} (hpositive : 0 < epsilon) (hthreshold : epsilon < epsilonStar) :
    0 < bk15Recurrence epsilon := by
  have hclean : 0 < 1 - epsilon := by
    linarith [hthreshold, epsilonStar_lt_half]
  let weightSum : Real :=
    35 * (epsilon ^ 3 * (1 - epsilon) ^ 12) +
      168 * (epsilon ^ 5 * (1 - epsilon) ^ 10) +
      435 * (epsilon ^ 7 * (1 - epsilon) ^ 8) +
      280 * (epsilon ^ 9 * (1 - epsilon) ^ 6) +
      105 * (epsilon ^ 11 * (1 - epsilon) ^ 4) + epsilon ^ 15
  have hfirst : 0 < 35 * (epsilon ^ 3 * (1 - epsilon) ^ 12) := by
    positivity
  have hrest : 0 <=
      168 * (epsilon ^ 5 * (1 - epsilon) ^ 10) +
        435 * (epsilon ^ 7 * (1 - epsilon) ^ 8) +
        280 * (epsilon ^ 9 * (1 - epsilon) ^ 6) +
        105 * (epsilon ^ 11 * (1 - epsilon) ^ 4) + epsilon ^ 15 := by
    positivity
  have hweightSum : 0 < weightSum := by
    dsimp [weightSum]
    linarith
  have hdenom := bk15Recurrence_scaled_denominator_pos epsilon
  unfold bk15Recurrence
  rw [bk15Recurrence_numerator_weight_sum]
  exact div_pos (mul_pos (by norm_num) hweightSum) hdenom
theorem bk15Recurrence_lt_input
    {epsilon : Real} (hpositive : 0 < epsilon) (hthreshold : epsilon < epsilonStar) :
    bk15Recurrence epsilon < epsilon := by
  have hbias_star_lt : bk15BiasStar < bk15Bias epsilon := by
    rw [← bk15Bias_epsilonStar]
    unfold bk15Bias
    linarith
  have hbias_one : bk15Bias epsilon < 1 := by
    unfold bk15Bias
    linarith
  have hpoly : 0 < bk15FixedPolynomial (bk15Bias epsilon) :=
    fixedPolynomial_pos_of_biasStar_lt hbias_star_lt hbias_one
  have hproduct : 0 < bk15Bias epsilon * bk15FixedPolynomial (bk15Bias epsilon) := by
    have hbias_pos : 0 < bk15Bias epsilon := bk15BiasStar_pos.trans hbias_star_lt
    positivity
  apply sub_neg.mp
  rw [bk15Recurrence_sub_input]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hproduct)
    (bk15Recurrence_scaled_denominator_pos epsilon)
def bk15Iteration (epsilon : Real) (rounds : Nat) : Real :=
  (bk15Recurrence^[rounds]) epsilon
theorem bk15Iteration_succ (epsilon : Real) (rounds : Nat) :
    bk15Iteration epsilon (rounds + 1) =
      bk15Recurrence (bk15Iteration epsilon rounds) := by
  rw [bk15Iteration, bk15Iteration, Function.iterate_succ_apply']
theorem bk15Iteration_pos_and_lt_epsilonStar
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) :
    0 < bk15Iteration epsilon rounds ∧
      bk15Iteration epsilon rounds < epsilonStar := by
  induction rounds with
  | zero => exact ⟨hpositive, hthreshold⟩
  | succ rounds ih =>
      rw [bk15Iteration_succ]
      constructor
      · exact bk15Recurrence_pos_of_pos_lt_epsilonStar ih.1 ih.2
      · exact (bk15Recurrence_lt_input ih.1 ih.2).trans ih.2
noncomputable def bk15IterationEpsilon
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) : BK15Epsilon where
  epsilon := bk15Iteration epsilon rounds
  nonneg := (bk15Iteration_pos_and_lt_epsilonStar
    epsilon hpositive hthreshold rounds).1.le
  le_half := (bk15Iteration_pos_and_lt_epsilonStar
    epsilon hpositive hthreshold rounds).2.trans epsilonStar_lt_half |>.le
noncomputable def bk15AcceptedLayer
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) :
    DensityOperator QubitSpace :=
  (bk15Run (bk15IterationEpsilon epsilon hpositive hthreshold rounds)
    (bk15Iteration_pos_and_lt_epsilonStar
      epsilon hpositive hthreshold rounds).1).acceptedOutput
def bk15CubicRatio (epsilon : Real) : Real :=
  16 *
      (35 * (1 - epsilon) ^ 12 +
        168 * (epsilon ^ 2 * (1 - epsilon) ^ 10) +
        435 * (epsilon ^ 4 * (1 - epsilon) ^ 8) +
        280 * (epsilon ^ 6 * (1 - epsilon) ^ 6) +
        105 * (epsilon ^ 8 * (1 - epsilon) ^ 4) + epsilon ^ 12) /
    (1 + 15 * bk15Bias epsilon ^ 8)
def bk15HInputError (rho : DensityOperator QubitSpace) : Real :=
  1 - hFidelity rho ^ 2
def FStar : Real := Real.sqrt (1 - epsilonStar)
noncomputable def bk15HInputEpsilon
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hleHalf : bk15HInputError rho <= 1 / 2) : BK15Epsilon :=
  hCanonicalizedInputEpsilon rho
    (by
      change 0 < bk15HInputError rho
      exact hpositive)
    (by
      change bk15HInputError rho <= 1 / 2
      exact hleHalf)
theorem bk15HInputEpsilon_pos
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hleHalf : bk15HInputError rho <= 1 / 2) :
    0 < (bk15HInputEpsilon rho hpositive hleHalf).epsilon := by
  change 0 < bk15HInputError rho
  exact hpositive
inductive BK15SemanticSchedule (rho : DensityOperator QubitSpace) : Nat -> Type
  | leaf (resource : DensityOperator QubitSpace) : BK15SemanticSchedule rho 0
  | accepted {depth : Nat}
      (children : Fin 15 -> BK15SemanticSchedule rho depth)
      (acceptedOutput : DensityOperator QubitSpace) :
      BK15SemanticSchedule rho (depth + 1)
namespace BK15SemanticSchedule
def leafCount {rho : DensityOperator QubitSpace} :
    {depth : Nat} -> BK15SemanticSchedule rho depth -> Nat
  | _, .leaf _ => 1
  | _, .accepted children _ => Finset.univ.sum fun site => leafCount (children site)
noncomputable def rootOutput {rho : DensityOperator QubitSpace} :
    {depth : Nat} -> BK15SemanticSchedule rho depth -> DensityOperator QubitSpace
  | _, .leaf resource => sourceA0Transport.conjDensity resource
  | _, .accepted _ acceptedOutput => acceptedOutput
noncomputable def rootInput {rho : DensityOperator QubitSpace} {depth : Nat}
    (schedule : BK15SemanticSchedule rho (depth + 1)) :
    ResourceInput 15 QubitSpace :=
  match schedule with
  | .accepted children _ => fun site =>
      aBasisDephasing.mapDensity (rootOutput (children site))
noncomputable def preparedInput {rho : DensityOperator QubitSpace} {depth : Nat}
    (schedule : BK15SemanticSchedule rho (depth + 1)) :
    DensityOperator BK15Register :=
  bk15PrepareInput (rootInput schedule)
end BK15SemanticSchedule
noncomputable def bk15CompleteSemanticSchedule
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) :
    (rounds : Nat) -> BK15SemanticSchedule rho rounds
  | 0 => .leaf (hCanonicalizedInput rho)
  | depth + 1 => .accepted
      (fun _ => bk15CompleteSemanticSchedule rho hpositive hthreshold depth)
      (bk15AcceptedLayer (bk15HInputError rho) hpositive hthreshold depth)
noncomputable def bk15AcceptedLayerHOutput
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) :
    DensityOperator QubitSpace :=
  sourceA0Transport.symm.conjDensity
    (bk15AcceptedLayer epsilon hpositive hthreshold rounds)
noncomputable def bk15IdealReturnedHOutput : DensityOperator QubitSpace :=
  sourceA0Transport.symm.conjDensity
    (decodedOperation.mapDensity (rawInput zeroEpsilon))
noncomputable def bk15AcceptedRunHOutput
    (rho : DensityOperator QubitSpace) (rounds : Nat) :
    DensityOperator QubitSpace :=
  if hstrict : 0 < bk15HInputError rho ∧ bk15HInputError rho < epsilonStar then
    match rounds with
    | 0 => hCanonicalizedInput rho
    | depth + 1 => sourceA0Transport.symm.conjDensity
        (BK15SemanticSchedule.rootOutput
          (bk15CompleteSemanticSchedule rho hstrict.1 hstrict.2 (depth + 1)))
  else if bk15HInputError rho = 0 then bk15IdealReturnedHOutput
  else hCanonicalizedInput rho
def bk15AcceptedRunHInfidelity
    (rho : DensityOperator QubitSpace) (rounds : Nat) : Real :=
  1 - hFidelity (bk15AcceptedRunHOutput rho rounds) ^ 2
end Threshold
end BK15
end Distillation
end QEC


