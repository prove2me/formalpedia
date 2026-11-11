-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
-- name    : QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T10:58:35.022928+00:00
-- url     : https://prove2.me/theorems/2ec7fba2-7493-4fef-af4c-dd792eb352c9
-- title:
--   Paired History Query Cone
-- statement:
--   Definitions and structural lemmas for Paired History Query Cone, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
abbrev TopWord (S : OddScale) (n : Nat) :=
  (SuffixData S n).family.Cochain1 (TopIndex n)
variable (S : OddScale) (n : Nat)
def potential (e : TopWord S n) (a : LevelIndex n) : Finset (Coordinates S n a) :=
  propagate S n n (Nat.le_refl _) a (Nat.le_of_lt_succ a.isLt)
    (hammingSupport ((SuffixData S n).family.coboundary1 (TopIndex n) e))
def querySeed (e : TopWord S n) (a : LevelIndex n) : Finset (Coordinates S n a) :=
  if a.val = 0 then Finset.univ else potential S n e a
def queryPrefix (e : TopWord S n) (a : LevelIndex n)
    (b : Nat) (hb : b ≤ n) : Finset (Coordinates S n ⟨b,Nat.lt_succ_of_le hb⟩) := by
  cases b with
  | zero =>
      if h : a.val = 0 then
        exact (show a = ⟨0,Nat.lt_succ_of_le hb⟩ from Fin.ext h) ▸ querySeed S n e a
      else exact ∅
  | succ b =>
      if h : a.val = b+1 then
        exact (show a = ⟨b+1,Nat.lt_succ_of_le hb⟩ from Fin.ext h) ▸ querySeed S n e a
      else if ha : a.val ≤ b then
        exact correctionQueries S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩)
          (potential S n e ⟨b+1,Nat.lt_succ_of_le hb⟩) ∪
          liftQueries S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩)
            (queryPrefix e a b (by omega))
      else exact ∅
termination_by b
def queries (e : TopWord S n) (a b : LevelIndex n) : Finset (Coordinates S n b) :=
  queryPrefix S n e a b.val (Nat.le_of_lt_succ b.isLt)
inductive QueryPath (e : TopWord S n) (a : LevelIndex n) :
    (b : LevelIndex n) → Coordinates S n b → Prop
  | seed (p : Coordinates S n a) (hp : p ∈ querySeed S n e a) : QueryPath e a a p
  | correction (i : StepIndex n) (ha : a.val ≤ i.val) (p : Coordinates S n i.succ)
      (hp : p ∈ correctionQueries S (n+2) (LevelTwoHistory.physicalStep i)
        (potential S n e i.succ)) : QueryPath e a i.succ p
  | lift (i : StepIndex n) (ha : a.val ≤ i.val) (z : Coordinates S n i.castSucc)
      (path : QueryPath e a i.castSucc z) (p : Coordinates S n i.succ)
      (hp : p ∈ coarseRead S (n+2) (LevelTwoHistory.physicalStep i) z) :
      QueryPath e a i.succ p
def coalescentLevels (s : TopInput S n) (e : TopWord S n) : Finset (LevelIndex n) :=
  Finset.univ.filter fun a => actualInputs S n s a = actualInputs S n (perturbTop S n s e) a
def stoppingLevel (s : TopInput S n) (e : TopWord S n) : LevelIndex n :=
  if h : (coalescentLevels S n s e).Nonempty then (coalescentLevels S n s e).max' h else 0
def budgetPrefix (e : TopWord S n) (a : LevelIndex n) (b : Nat) (hb : b ≤ n) : Nat := by
  cases b with
  | zero => exact if a.val = 0 then (querySeed S n e a).card else 0
  | succ b =>
      exact if a.val = b+1 then (querySeed S n e a).card else
        if a.val ≤ b then queryBlockBound S *
          (57 * (potential S n e ⟨b+1,Nat.lt_succ_of_le hb⟩).card +
            budgetPrefix e a b (by omega)) else 0
termination_by b
def windowBudget (S : OddScale) (L w : Nat) : Nat :=
  (57 * queryBlockBound S + 1) * (57^L*w) * (queryBlockBound S+1)^L
end QEC.Coding.BDL26PairedHistoryQueryCone


