-- Prove2me | Definitions.Def_QEC_Results_Distillation_PrimeQuditOverhead
-- name    : QEC_Results_Distillation_PrimeQuditOverhead
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T11:28:30.005757+00:00
-- url     : https://prove2.me/theorems/3c02c168-0f63-4506-9f45-8368fdedf5ee
-- title:
--   Prime Qudit Overhead
-- statement:
--   Definitions and structural lemmas for Prime Qudit Overhead, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/PrimeQuditOverhead.lean

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_VanishingOverhead
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_apply
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_childInputSlot
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_kt19Routing_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryDistillationRun_successProbability
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_zero
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_apply
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_childInputSlot
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.KT19Protocol.KT19DistillationFamily.kt19Routing_apply
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.binaryDistillationRun_successProbability
attribute [local simp] QEC.Semantics.FiniteInstrument.branchOperator_zero
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.KT19VanishingOverhead
open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19Protocol
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open Filter Topology
open scoped BigOperators
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
section PrimeQuditOverheadPrivateHelpers
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
attribute [local instance] QEC.Distillation.KT19VanishingOverhead.instKT19VanishingOverheadClassicalDecidable
noncomputable def primeQuditOverhead_kt19FixedPrimeIterationScale
    (family : KT19DistillationFamily p l k) : ℝ :=
  KT19DistillationFamily.smallErrorRecurrenceConstant family +
    4 * ((p - k : Nat) : ℝ) + 1
theorem primeQuditOverhead_kt19FixedPrimeRecurrenceConstant_nonneg
    (family : KT19DistillationFamily p l k) :
    0 ≤ KT19DistillationFamily.smallErrorRecurrenceConstant family := by
  unfold KT19DistillationFamily.smallErrorRecurrenceConstant
  positivity
theorem primeQuditOverhead_kt19FixedPrimeIterationScale_one_le
    (family : KT19DistillationFamily p l k) :
    1 ≤ primeQuditOverhead_kt19FixedPrimeIterationScale family := by
  unfold primeQuditOverhead_kt19FixedPrimeIterationScale
  have hcount_nonneg : (0 : ℝ) ≤ ((p - k : Nat) : ℝ) := Nat.cast_nonneg _
  nlinarith [primeQuditOverhead_kt19FixedPrimeRecurrenceConstant_nonneg family, hcount_nonneg]
theorem primeQuditOverhead_kt19FixedPrimeIterationScale_pos
    (family : KT19DistillationFamily p l k) :
    0 < primeQuditOverhead_kt19FixedPrimeIterationScale family :=
  lt_of_lt_of_le zero_lt_one (primeQuditOverhead_kt19FixedPrimeIterationScale_one_le family)
noncomputable def primeQuditOverhead_kt19FixedPrimeLogGrowthBase
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ) : ℝ :=
  -Real.log (primeQuditOverhead_kt19FixedPrimeIterationScale family * kt19ErrorRate mu)
noncomputable def primeQuditOverhead_kt19SmallIIDRate
    (family : KT19DistillationFamily p l k) : ℝ :=
  1 / (4 * primeQuditOverhead_kt19FixedPrimeIterationScale family)
noncomputable def primeQuditOverhead_kt19SmallIIDLaw
    (family : KT19DistillationFamily p l k) : ZMod p → ℝ :=
  fun a => if a = 0 then 1 - primeQuditOverhead_kt19SmallIIDRate family
    else if a = 1 then primeQuditOverhead_kt19SmallIIDRate family else 0
theorem primeQuditOverhead_kt19SmallIIDRate_pos
    (family : KT19DistillationFamily p l k) :
    0 < primeQuditOverhead_kt19SmallIIDRate family := by
  unfold primeQuditOverhead_kt19SmallIIDRate
  exact one_div_pos.mpr
    (mul_pos (by norm_num) (primeQuditOverhead_kt19FixedPrimeIterationScale_pos family))
theorem primeQuditOverhead_kt19SmallIIDRate_le_one
    (family : KT19DistillationFamily p l k) :
    primeQuditOverhead_kt19SmallIIDRate family ≤ 1 := by
  unfold primeQuditOverhead_kt19SmallIIDRate
  have hden : (1 : ℝ) ≤ 4 * primeQuditOverhead_kt19FixedPrimeIterationScale family := by
    have hscale : (1 : ℝ) ≤ primeQuditOverhead_kt19FixedPrimeIterationScale family :=
      primeQuditOverhead_kt19FixedPrimeIterationScale_one_le family
    nlinarith
  exact (one_div_le_one_div_of_le (by norm_num) hden).trans_eq (by norm_num)
theorem primeQuditOverhead_kt19SmallIIDLaw_nonneg
    (family : KT19DistillationFamily p l k) (a : ZMod p) :
    0 ≤ primeQuditOverhead_kt19SmallIIDLaw family a := by
  unfold primeQuditOverhead_kt19SmallIIDLaw
  split_ifs
  · exact sub_nonneg.mpr (primeQuditOverhead_kt19SmallIIDRate_le_one family)
  · exact (primeQuditOverhead_kt19SmallIIDRate_pos family).le
  · exact le_rfl
theorem primeQuditOverhead_kt19SmallIIDLaw_sum
    (family : KT19DistillationFamily p l k) [Fact p.Prime] :
    ∑ a : ZMod p, primeQuditOverhead_kt19SmallIIDLaw family a = 1 := by
  classical
  let support : Finset (ZMod p) :=
    (Finset.univ.erase (0 : ZMod p)).erase 1
  have hsupport : ∑ a ∈ support, primeQuditOverhead_kt19SmallIIDLaw family a = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have haone : a ≠ 1 := (Finset.mem_erase.mp ha).1
    have hazero : a ≠ 0 :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    simp [primeQuditOverhead_kt19SmallIIDLaw, hazero, haone]
  calc
    ∑ a : ZMod p, primeQuditOverhead_kt19SmallIIDLaw family a =
        (∑ a ∈ Finset.univ.erase (0 : ZMod p), primeQuditOverhead_kt19SmallIIDLaw family a) +
          primeQuditOverhead_kt19SmallIIDLaw family 0 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
    _ = (∑ a ∈ support, primeQuditOverhead_kt19SmallIIDLaw family a) +
          primeQuditOverhead_kt19SmallIIDLaw family 1 + primeQuditOverhead_kt19SmallIIDLaw family 0 := by
      rw [← Finset.sum_erase_add (a := (1 : ZMod p))
        (Finset.univ.erase (0 : ZMod p)) _ (by simp)]
    _ = 1 := by
      rw [hsupport]
      simp [primeQuditOverhead_kt19SmallIIDLaw]
end PrimeQuditOverheadPrivateHelpers
end QEC.Distillation.KT19VanishingOverhead


