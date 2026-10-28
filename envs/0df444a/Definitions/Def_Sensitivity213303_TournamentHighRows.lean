-- Prove2me | Definitions.Def_Sensitivity213303_TournamentHighRows
-- name    : Sensitivity213303_TournamentHighRows
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T21:33:55.98626+00:00
-- url     : https://prove2.me/theorems/bddd1ea4-4a43-4c0e-8fd7-05ca1f31d8d2
-- title:
--   Tournament orientations and actual selected-child guard failures
-- statement:
--   A tournament relation is loopless and gives exactly one orientation to every pair of distinct vertices. For a finite set of vertices, outNeighbors records outgoing neighbors and arcs records directed internal edges. Given a binary edge labeling, a guard predicate and two children per vertex, guardFailures(v) is the set of outgoing neighbors whose edge-selected child satisfies the guard predicate. These actual failure sets connect the Boolean construction to tournament edge-counting bounds.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module TournamentHighRows; source SHA256 33af55a94cc9e5226b2ef38c43cfae605b761c3b899fa90837313bdcbcfd382f.

/-
Semantic high-row bounds for the graded q2/q3 transfer.

The finite high set is connected to actual guard failure sets: every arc to
a high head selects a guard-true child and therefore consumes a failure of
its tail. The tournament edge double count is proved here, not assumed.
-/
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith



set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace TournamentHighRows
open scoped Classical BigOperators

variable {V X : Type}

/-- The two tournament axioms used in the counting proof. -/
structure IsTournament (R : V → V → Prop) : Prop where
  loopless : ∀ v, ¬ R v v
  orient : ∀ v w, v ≠ w → (R v w ↔ ¬ R w v)

noncomputable def outNeighbors (R : V → V → Prop) (S : Finset V) (v : V) : Finset V := by
  classical
  exact S.filter (R v)

noncomputable def arcs (R : V → V → Prop) (S : Finset V) : Finset (V × V) := by
  classical
  exact (S.product S).filter fun p => R p.1 p.2



















section GuardSemantics
variable [Fintype V]

/-- The actual failures of a selected-child guard at a row. -/
noncomputable def guardFailures (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun w => R v w ∧ P (children w (ell v w))













end GuardSemantics
end TournamentHighRows


