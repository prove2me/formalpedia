-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
-- name    : QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T06:23:50.118112+00:00
-- url     : https://prove2.me/theorems/79bbf5d1-8b40-485d-a37e-bb031acd1d8c
-- title:
--   Intervals
-- statement:
--   Definitions and structural lemmas for Intervals, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Order.Interval.Finset.Nat
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
abbrev Coordinates (a : LevelIndex n) :=
  FamilyZ S (n+2) (LevelTwoHistory.physicalLevel a)
def rxCount (a b : Nat) : Nat :=
  ((Finset.Ico a b).filter (fun k => k % 2 = 0)).card
def propagate (b : Nat) (hb : b ≤ n) (a : LevelIndex n) (ha : a.val ≤ b)
    (A : Finset (Coordinates S n ⟨b,Nat.lt_succ_of_le hb⟩)) :
    Finset (Coordinates S n a) := by
  cases b with
  | zero =>
      exact (show (⟨0,Nat.lt_succ_of_le hb⟩ : LevelIndex n) = a from
        Fin.ext (by change 0 = a.val; omega)) ▸ A
  | succ b =>
      if h : a.val = b+1 then
        exact (show (⟨b+1,Nat.lt_succ_of_le hb⟩ : LevelIndex n) = a from
          Fin.ext h.symm) ▸ A
      else
        exact propagate b (by omega) a (by omega)
          (stepPropagation S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩) A)
termination_by b
end QEC.Coding.BDL26HistorySyndromeSensitivity


