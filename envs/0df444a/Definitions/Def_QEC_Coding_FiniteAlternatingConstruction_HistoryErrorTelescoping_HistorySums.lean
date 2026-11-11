-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
-- name    : QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T06:26:48.032631+00:00
-- url     : https://prove2.me/theorems/feb4535d-70dc-47c8-94fb-894275a9d84c
-- title:
--   History Sums
-- statement:
--   Definitions and structural lemmas for History Sums, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26DecodingGraph
open scoped Classical
universe u v
section Lists
variable {A : Type u} {W : Type v} [AddCommMonoid W]
end Lists
section OriginalLists
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
def prefixEntry (D : BDL26DecoderData depth C0 C1 C2)
    (b : LevelIndex depth) : CorrectionHistoryEntry D → Option (D.family.Cochain1 b)
  | .base B => some (intervalMap1 D 0 b (Nat.zero_le _) B.correction)
  | .step i O => if h : i.succ.val ≤ b.val then
      some (intervalMap1 D i.succ b h O.correction) else none
def intervalEntry (D : BDL26DecoderData depth C0 C1 C2)
    (a b : LevelIndex depth) : CorrectionHistoryEntry D → Option (D.family.Cochain1 b)
  | .base _ => none
  | .step i O => if h : a.val < i.succ.val ∧ i.succ.val ≤ b.val then
      some (intervalMap1 D i.succ b h.2 O.correction) else none
def historyPrefixSum (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (b : LevelIndex depth) : D.family.Cochain1 b :=
  (H.filterMap (prefixEntry D b)).sum
def historyIntervalSum (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (a b : LevelIndex depth) : D.family.Cochain1 b :=
  (H.filterMap (intervalEntry D a b)).sum
def historyThrough (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (b : LevelIndex depth) : CorrectionHistory D :=
  H.filter (fun e => decide (e.level ≤ b.val))
end OriginalLists
section ActualHistory
variable (S : OddScale) (n : Nat)
def actualOutput (sigma : TopInput S n) (i : StepIndex n) :
    AssemblyStepOutput (SuffixData S n) i :=
  (LevelTwoHistory.suffixSteps (indexedDecoderData S (n+2))
    (actualAboveTwoSteps S n)).step i (actualInputs S n sigma i.succ)
def correctionIntervalSum (sigma : TopInput S n) (a b : LevelIndex n) :
    (SuffixData S n).family.Cochain1 b :=
  historyIntervalSum (SuffixData S n) (actualHistory S n sigma) a b
def assembledPrefix (sigma : TopInput S n) (b : LevelIndex n) :
    (SuffixData S n).family.Cochain1 b :=
  historyPrefixSum (SuffixData S n) (actualHistory S n sigma) b
def snapshotWords (sigma : TopInput S n) (a : LevelIndex n)
    (b : Nat) (hb : b ≤ n) (ha : a.val ≤ b) :
    List ((SuffixData S n).family.Cochain1 ⟨b,Nat.lt_succ_of_le hb⟩) := by
  cases b with
  | zero => exact []
  | succ b =>
      if h : a.val = b+1 then exact []
      else
        let i : StepIndex n := ⟨b,Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb⟩
        exact (actualOutput S n sigma i).correction ::
          (snapshotWords sigma a b (by omega) (by omega)).map ((SuffixData S n).selectedMap i).map1
termination_by b
end ActualHistory
end QEC.Coding.BDL26HistoryErrorTelescoping


