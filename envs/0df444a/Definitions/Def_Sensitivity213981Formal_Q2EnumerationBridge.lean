-- Prove2me | Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
-- name    : Sensitivity213981Formal_Q2EnumerationBridge
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T19:43:34.533798+00:00
-- url     : https://prove2.me/theorems/d582a380-1cc9-4886-8c23-4807ec54108b
-- title:
--   Q2 Enumeration Bridge — sensitivity certificate definitions
-- statement:
--   The definitions for Q2 Enumeration Bridge in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundQ2.orientationBits`, `ThreeBoundQ2.orientEdge`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Q2EnumerationBridge.lean, lines 1–245.

import Definitions.Def_Sensitivity213981Formal_GuardAugmentation
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_Q2Enumeration
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
/-
Canonical numbering and actual tournament-degree bridge for the executable
q2 enumerator.  This connects combinatorial coverage to finite tournaments,
without replacing sensitivity charging by numerical assumptions.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundQ2
open scoped Classical BigOperators







def orientationBits {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] : List Bool :=
  (edges n).map fun e => decide (R e.2 e.1)

def orientEdge {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (e : Fin n × Fin n) : Fin n × Fin n :=
  if R e.2 e.1 then e.swap else e





















end ThreeBoundQ2





end
end Sensitivity213981Formal


