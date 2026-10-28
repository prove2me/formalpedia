-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22TypeSplit
-- name    : Sensitivity213981Formal_Endpoint22TypeSplit
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:27:45.205349+00:00
-- url     : https://prove2.me/theorems/d3587988-8ddf-4846-a164-8ec02b141882
-- title:
--   Endpoint22 Type Split — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Type Split in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22TypeSplit.filteredPrefix`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22TypeSplit.lean, lines 1–62.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedRecordCoverage
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- Split the exact active-type enumeration into small, independently checked
prefixes. This changes no enumeration predicate or final equality statement. -/


set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

namespace ThreeBoundEndpoint22TypeSplit
open ThreeBoundQ3

def filteredPrefix (pref : List Kind) (lo n : ℕ) : List (List Kind) :=
  ((typeLists lo n).map (fun ts => pref ++ ts)).filter
    (fun ts => decide (allowedTypes ts))







end ThreeBoundEndpoint22TypeSplit




end
end Sensitivity213981Formal


