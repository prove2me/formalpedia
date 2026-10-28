-- Prove2me | Definitions.Def_Sensitivity213981Formal_RelaxedRecordCoverage
-- name    : Sensitivity213981Formal_RelaxedRecordCoverage
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:30:49.683663+00:00
-- url     : https://prove2.me/theorems/aa84f432-d530-4897-bbe9-caa542bbbe81
-- title:
--   Relaxed Record Coverage — sensitivity certificate definitions
-- statement:
--   The definitions for Relaxed Record Coverage in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRelaxedCoverage.activeTypes`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RelaxedRecordCoverage.lean, lines 1–64.

import Definitions.Def_Sensitivity213981Formal_Endpoint22RegularRecord
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedOrientation
import Definitions.Def_Sensitivity213981Formal_Supplement_RecordSetLookup
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
/- Composition of the canonical degree-state cover with finite lookup checks. -/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundRelaxedCoverage
open ThreeBoundQ3 ThreeBoundRelaxed

def activeTypes (n : ℕ) : List (List Kind) :=
  (ThreeBoundQ3.typeLists 0 n).filter fun ts => decide (allowedTypes ts)









end ThreeBoundRelaxedCoverage



end
end Sensitivity213981Formal


