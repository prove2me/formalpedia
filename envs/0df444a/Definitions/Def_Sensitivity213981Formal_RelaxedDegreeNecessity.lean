-- Prove2me | Definitions.Def_Sensitivity213981Formal_RelaxedDegreeNecessity
-- name    : Sensitivity213981Formal_RelaxedDegreeNecessity
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:07:42.971629+00:00
-- url     : https://prove2.me/theorems/87eaf1e9-a6f5-4aec-99d6-1f0b48775066
-- title:
--   Relaxed Degree Necessity — sensitivity certificate definitions
-- statement:
--   The definitions for Relaxed Degree Necessity in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRelaxedDegree.outDegree`, `ThreeBoundRelaxedDegree.guardIncoming`, `ThreeBoundRelaxedDegree.indicator`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RelaxedDegreeNecessity.lean, lines 1–125.

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- Necessary degree and guard-incoming statistics of every actual tournament.
These exact identities justify the finite relaxed-state coverage checker. -/


set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundRelaxedDegree
open TournamentHighRows
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V]

def outDegree (R : V → V → Prop) (v : V) : ℕ := (Finset.univ.filter (R v)).card
def guardIncoming (R : V → V → Prop) (G : Finset V) (v : V) : ℕ :=
  (G.filter fun u => R u v).card
def indicator (G : Finset V) (v : V) : ℕ := if v ∈ G then 1 else 0





















end
end ThreeBoundRelaxedDegree




end
end Sensitivity213981Formal


