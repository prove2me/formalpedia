-- Prove2me | Definitions.Def_Sensitivity213981Formal_TournamentHighRows
-- name    : Sensitivity213981Formal_TournamentHighRows
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T17:09:57.698546+00:00
-- url     : https://prove2.me/theorems/ce8d8d20-2cc9-4526-9d17-4be7a04b1ad4
-- title:
--   Tournament High Rows — sensitivity certificate definitions
-- statement:
--   The definitions for Tournament High Rows in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `TournamentHighRows.guardFailures`, `TournamentHighRows.IsTournament`, `TournamentHighRows.outNeighbors`, `TournamentHighRows.arcs`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; TournamentHighRows.lean, lines 1–240.

import Definitions.Def_Sensitivity213981Formal_MinmaxLocal
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith

namespace Sensitivity213981Formal
section
/-
Semantic high-row bounds for the graded q2/q3 transfer.

The finite high set is connected to actual guard failure sets: every arc to
a high head selects a guard-true child and therefore consumes a failure of
its tail. The tournament edge double count is proved here, not assumed.
-/


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








end
end Sensitivity213981Formal


