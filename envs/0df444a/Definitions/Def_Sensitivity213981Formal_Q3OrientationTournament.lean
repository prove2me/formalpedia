-- Prove2me | Definitions.Def_Sensitivity213981Formal_Q3OrientationTournament
-- name    : Sensitivity213981Formal_Q3OrientationTournament
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:06:51.489512+00:00
-- url     : https://prove2.me/theorems/9a21aa2b-2139-4a46-9b4d-fcdb6382db1a
-- title:
--   Q3 Orientation Tournament — sensitivity certificate definitions
-- statement:
--   The definitions for Q3 Orientation Tournament in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundOrientation.direction`, `ThreeBoundOrientation.relation`, `ThreeBoundOrientation.instDecidableRelFinRelation`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Q3OrientationTournament.lean, lines 1–70.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
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
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace Sensitivity213981Formal
section
/- Every full edge-bit list encodes an actual tournament. This inverse bridge
   lets finite enumeration certificates use ordinary tournament counting. -/


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ThreeBoundOrientation
open ThreeBoundQ2

def direction {n : ℕ} (ds : List Bool) (e : Fin n × Fin n) : Bool :=
  (ds[(edges n).idxOf e]?).getD false

def relation {n : ℕ} (ds : List Bool) (v w : Fin n) : Prop :=
  (v <  w ∧ direction ds (v,w) = false) ∨
  (w <  v ∧ direction ds (w,v) = true)

instance _root_.Sensitivity213981Formal.ThreeBoundOrientation.instDecidableRelFinRelation {n : ℕ} (ds : List Bool) : DecidableRel (relation (n := n) ds) := by
  unfold relation
  infer_instance











end ThreeBoundOrientation




end
end Sensitivity213981Formal


