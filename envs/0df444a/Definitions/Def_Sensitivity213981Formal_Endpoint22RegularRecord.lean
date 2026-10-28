-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22RegularRecord
-- name    : Sensitivity213981Formal_Endpoint22RegularRecord
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:07:33.258783+00:00
-- url     : https://prove2.me/theorems/2f81fcba-31e8-404c-825e-ac6c92667fa0
-- title:
--   Endpoint22 Regular Record — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Regular Record in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Regular.allG3`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22RegularRecord.lean, lines 1–110.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_Q3RecordFields
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
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- The saturated nine-guard case has a single exact record, independently
of its orientation.  This replaces exhaustive reductions of regular tournaments. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 200000

namespace ThreeBoundEndpoint22Regular
open ThreeBoundQ3 ThreeBoundQ3RecordFields ThreeBoundSaturated

def allG3 : List Kind := List.replicate 9 7


















end ThreeBoundEndpoint22Regular






end
end Sensitivity213981Formal


