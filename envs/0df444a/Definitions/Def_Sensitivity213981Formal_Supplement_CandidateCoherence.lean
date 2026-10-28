-- Prove2me | Definitions.Def_Sensitivity213981Formal_Supplement_CandidateCoherence
-- name    : Sensitivity213981Formal_Supplement_CandidateCoherence
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T18:24:08.714604+00:00
-- url     : https://prove2.me/theorems/b06bab69-e2e9-42fe-ac54-d1bf0c0d1044
-- title:
--   Supplement Candidate Coherence — sensitivity certificate definitions
-- statement:
--   The definitions for Candidate Coherence in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `CandidateCoherence.targetColor`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; CandidateCoherence.lean, lines 1–189.

import Definitions.Def_Sensitivity213981Formal_CandidateCoherence
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



/-- Choose the position opposite an accepted lower-target child. -/
noncomputable def targetColor (F : Fin N → X → Prop) (t : V → Fin N)
    (children : V → Bool → X) (v : V) : Bool := by
  classical
  exact if F (t v) (children v false) then true else false



















section ActualGuards
variable [Fintype V]











end ActualGuards
end CandidateCoherence







end
end Sensitivity213981Formal


