-- Prove2me | Definitions.Def_Sensitivity213981Formal_RelaxedPackedTreeMatch
-- name    : Sensitivity213981Formal_RelaxedPackedTreeMatch
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:26:40.023356+00:00
-- url     : https://prove2.me/theorems/50ba2a77-22ee-4773-90b6-db60eb093290
-- title:
--   Relaxed Packed Tree Match — sensitivity certificate definitions
-- statement:
--   The definitions for Relaxed Packed Tree Match in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRelaxedPacked.Tree.Matches`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RelaxedPackedTreeMatch.lean, lines 1–24.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedPackedTreeData
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
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace Sensitivity213981Formal
section

set_option autoImplicit false
namespace ThreeBoundRelaxedPacked
open ThreeBoundEndpoint22Records (decodeRow)
def Tree.Matches : Tree → ThreeBoundRecordLookup.Tree → Prop
  | .leaf _ code,.leaf row => decodeRow 41 code=row
  | .branch _ l r,.branch _ l' r' => l.Matches l' ∧ r.Matches r'
  | _,_ => False


end ThreeBoundRelaxedPacked

end
end Sensitivity213981Formal


