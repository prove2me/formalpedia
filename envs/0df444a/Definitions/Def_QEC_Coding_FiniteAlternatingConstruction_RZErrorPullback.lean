-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
-- name    : QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T06:07:08.642557+00:00
-- url     : https://prove2.me/theorems/ed95d1b4-5f98-4122-8a32-c958c178c633
-- title:
--   RZError Pullback
-- statement:
--   Definitions and structural lemmas for RZError Pullback, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RZErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RZCohomology BDL26AlternatingCochain
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
abbrev Lower := (indexedFamily S depth).Correction i.castSucc
abbrev Upper := (indexedFamily S depth).Correction i.succ
abbrev Potential := (indexedFamily S depth).Cochain0 i.succ
def errorSyndrome (a : Upper S depth i) : (indexedFamily S depth).Syndrome i.succ :=
  ⟨(indexedFamily S depth).coboundary1 i.succ a, ⟨a, rfl⟩⟩
def run (h : ¬ i.val % 2 = 0) (a : Upper S depth i) :
    AssemblyStepOutput (indexedDecoderData S depth) i :=
  BDL26RZDecoderAdapter.rzStepOutput S depth i h (errorSyndrome S depth i a)
def updated (h : ¬ i.val % 2 = 0) (a b : Upper S depth i) : Upper S depth i :=
  a + b + (run S depth i h a).correction + (run S depth i h b).correction
def coarseSum (h : ¬ i.val % 2 = 0) (a b : Upper S depth i) :
    (indexedFamily S depth).Syndrome i.castSucc :=
  ⟨(run S depth i h a).coarse.val + (run S depth i h b).coarse.val,
    ((indexedFamily S depth).syndromeSubmodule i.castSucc).add_mem
      (run S depth i h a).coarse.property (run S depth i h b).coarse.property⟩
section History
variable (n : Nat) (sigma : BDL26CanonicalHistoryMarks.Input S n) (k : StepIndex n)
end History
end QEC.Coding.BDL26RZErrorPullback


