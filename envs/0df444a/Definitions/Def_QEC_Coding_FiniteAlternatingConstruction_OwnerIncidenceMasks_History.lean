-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
-- name    : QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T05:57:09.326196+00:00
-- url     : https://prove2.me/theorems/d766ea29-f6d3-4aa9-b431-180fa33935e6
-- title:
--   History
-- statement:
--   Definitions and structural lemmas for History, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/History.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_decode_rightInverse
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_assembly_relation

set_option autoImplicit false
namespace QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open MultiscaleDecoder
open scoped Classical
noncomputable def actualStep (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    AssemblyStep (indexedDecoderData S depth) i :=
  fun sigma => if h : i.val % 2 = 0 then BDL26RXDecoderAdapter.rxStepOutput S depth i h sigma
  else BDL26RZDecoderAdapter.rzStepOutput S depth i h sigma
theorem actualStep_rx (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) :
    actualStep S depth i = BDL26RXDecoderAdapter.rxStepOutput S depth i h := by
  funext sigma
  exact dif_pos h
theorem actualStep_rz (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : ¬i.val % 2 = 0) :
    actualStep S depth i = BDL26RZDecoderAdapter.rzStepOutput S depth i h := by
  funext sigma
  exact dif_neg h
theorem actualStep_relation (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    AssemblyStepRelation (indexedDecoderData S depth) i (actualStep S depth i) := by
  by_cases h : i.val % 2 = 0
  · rw [actualStep_rx S depth i h]
    exact BDL26RXDecoderAdapter.rxStepOutput_assembly_relation S depth i h
  · rw [actualStep_rz S depth i h]
    refine ⟨?_, ?_⟩
    · intro sigma
      rfl
    · intro sigma
      exact (BDL26RZDecoderAdapter.rzStepOutput S depth i h sigma).relation
noncomputable def actualAboveTwoSteps (S : OddScale) (n : Nat) :
    LevelTwoHistory.AboveTwoSteps (indexedDecoderData S (n + 2)) where
  step := fun i _ => actualStep S (n + 2) i
  relation := fun i _ => actualStep_relation S (n + 2) i
noncomputable def actualBaseDecode (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n))) :
    (indexedFamily S (n + 2)).Correction
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n)) :=
  BDL26LevelTwoDecoder.decode S sigma.val
theorem actualBaseDecode_rightInverse (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n))) :
    (indexedFamily S (n + 2)).coboundary1
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n))
      (actualBaseDecode S n sigma) = sigma.val := by
  rw [indexedFamily_coboundary1]
  apply BDL26LevelTwoDecoder.decode_rightInverse
  have hs : sigma.val ∈ LinearMap.range ((indexedFamily S (n + 2)).coboundary1
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n))) := sigma.property
  rw [indexedFamily_coboundary1] at hs
  exact hs
noncomputable def actualBase (S : OddScale) (n : Nat) :
    AuditedBaseDecoder (LevelTwoHistory.suffixData (indexedDecoderData S (n + 2))) :=
  LevelTwoHistory.suffixBase _ (actualBaseDecode S n) (actualBaseDecode_rightInverse S n)
noncomputable def actualHistory (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2))) :
    CorrectionHistory (LevelTwoHistory.suffixData (indexedDecoderData S (n + 2))) :=
  LevelTwoHistory.stoppedHistory _ (actualAboveTwoSteps S n) (actualBase S n) sigma
end QEC.Coding.BDL26OwnerIncidenceMasks


