-- Prove2me | Definitions.Def_Sensitivity213981Formal_CandidateCoherence
-- name    : Sensitivity213981Formal_CandidateCoherence
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T17:11:01.7629+00:00
-- url     : https://prove2.me/theorems/c27a0985-701d-4c5e-87fb-75d2eec660fd
-- title:
--   Candidate Coherence — sensitivity certificate definitions
-- statement:
--   The definitions for Candidate Coherence in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `CandidateCoherence.mismatch`, `CandidateCoherence.OrdinaryGood`, `CandidateCoherence.NoOrdinary`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; CandidateCoherence.lean, lines 1–189.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_TournamentHighRows
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
The graded-target to labeling-exclusion bridge.

Targets at different rows may use different lower thresholds. A geometric
one-child candidate has an accepted partner; coloring its row by the other
position makes every label mismatch an actual guard failure. This argument
is independent of fixed versus graded targets and applies to min/max targets.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CandidateCoherence
open scoped Classical
open MinmaxLocal TournamentHighRows

variable {N : ℕ} {V X : Type}











noncomputable def mismatch (R : V → V → Prop) (ell : V → V → Bool)
    (T : Finset V) (color : V → Bool) (v : V) : Finset V := by
  classical
  exact T.filter fun w => R v w ∧ ell v w ≠ color w

def OrdinaryGood (R : V → V → Prop) (ell : V → V → Bool)
    (T : Finset V) (q : ℕ) (color : V → Bool) : Prop :=
  ∀ v ∈ T, (mismatch R ell T color v).card ≤ q

/-- An exact-size ordinary exclusion, in the same coloring semantics as the
    accepted labeling construction. -/
def NoOrdinary (R : V → V → Prop) (ell : V → V → Bool) (q a : ℕ) : Prop :=
  ∀ T : Finset V, T.card = a → ∀ color : V → Bool, ¬ OrdinaryGood R ell T q color







section ActualGuards
variable [Fintype V]











end ActualGuards
end CandidateCoherence







end
end Sensitivity213981Formal


