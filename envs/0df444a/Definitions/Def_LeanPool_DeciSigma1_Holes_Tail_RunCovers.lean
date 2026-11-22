-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
-- name    : LeanPool_DeciSigma1_Holes_Tail_RunCovers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:55:42.964074+00:00
-- url     : https://prove2.me/theorems/e909007d-127a-4c43-bf77-ca1ac2c35a72
-- title:
--   Run Covers
-- statement:
--   Definitions and structural lemmas for Run Covers, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RunCovers.lean

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayFamilies
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
structure RunSpec (k : ℕ) where
  /-- Coordinate whose word contains the run. -/
  coordinate : Fin k
  /-- First position of the run. -/
  start : ℕ
  /-- Position immediately after the run. -/
  stop : ℕ
  /-- Period assigned to the run. -/
  period : ℕ
  deriving DecidableEq
section Runs
def IsBoundedRun (U : Fin k → List α) (D : ℕ) (r : RunSpec k) : Prop :=
  IsPeriodicPiece U r.period r.coordinate r.start r.stop ∧ r.period ≤ D ∧ 2 * D ≤ r.stop - r.start
def RunCovers (runs : Finset (RunSpec k)) (i : Fin k) (p : ℕ) : Prop :=
  ∃ r ∈ runs, r.coordinate = i ∧ r.start ≤ p ∧ p < r.stop
instance (runs : Finset (RunSpec k)) (i : Fin k) (p : ℕ) : Decidable (RunCovers runs i p) :=
  inferInstanceAs (Decidable (∃ r ∈ runs, _))
def uncoveredTailPositions (M : StructuralReader α S k) (U : Fin k → List α)
    (runs : Finset (RunSpec k)) (i : Fin k) :
    Finset ℕ :=
  (Finset.Ico (M.firstRejection U i) (U i).length).filter (fun p => ¬ RunCovers runs i p)
def HasBoundedRunCover (M : StructuralReader α S k)
    (U : Fin k → List α)
    (n D E : ℕ) : Prop := by
  classical
  exact ∃ runs : Finset (RunSpec k), runs.card ≤ n ∧ (∀ r ∈ runs, IsBoundedRun U D r) ∧
    ∑ i, (if M.Immortal (M.endState U i) then (uncoveredTailPositions M U runs i).card else 0) ≤ E
def HasScaledRunCover (M : StructuralReader α S k)
    (U : Fin k → List α) (R D E : ℕ) : Prop :=
  HasBoundedRunCover M U (k * R) D E
end Runs
def uncoveredLengthBound {σ N : ℕ} (C : LevelBounds σ k N) : ℕ :=
  k * (C.uncoveredBound (levelCount k) + (C.pieceCountBase + 3) * (3 * C.escapeLengthBound
      (levelCount k) + 3) + (C.pieceCountBase + 3) * (2 * C.periodBound (levelCount k)))
section Assembly
variable [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S]
end Assembly
end DeciSigma1.Holes.Tail


