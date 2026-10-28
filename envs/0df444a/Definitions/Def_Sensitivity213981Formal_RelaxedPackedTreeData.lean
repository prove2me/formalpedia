-- Prove2me | Definitions.Def_Sensitivity213981Formal_RelaxedPackedTreeData
-- name    : Sensitivity213981Formal_RelaxedPackedTreeData
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:13:43.655207+00:00
-- url     : https://prove2.me/theorems/2ae5cbce-1659-4ac0-aa88-cd1a1c5ac644
-- title:
--   Relaxed Packed Tree Data — sensitivity certificate definitions
-- statement:
--   The definitions for Relaxed Packed Tree Data in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRelaxedPacked.keyAux`, `ThreeBoundRelaxedPacked.keyOfCode`, `ThreeBoundRelaxedPacked.Tree`, `ThreeBoundRelaxedPacked.Tree.erase`, `ThreeBoundRelaxedPacked.Tree.rows`, `ThreeBoundRelaxedPacked.Tree.contains`, `ThreeBoundRelaxedPacked.Tree.checkKeys`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RelaxedPackedTreeData.lean, lines 1–31.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedPackedRecords
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
def keyAux : ℕ → ℕ → ℕ → ℕ
  | 0,_,acc => acc
  | n+1,code,acc => keyAux n (code/16) (acc*radix+(if code%16=15 then 1000000 else code%16))

def keyOfCode (n code : ℕ) : ℕ := keyAux n code 0

inductive Tree where
  | leaf (key code : ℕ) : Tree
  | branch (pivot : ℕ) (left right : Tree) : Tree

def Tree.erase : Tree → ThreeBoundRecordLookup.Tree
  | .leaf _ code => .leaf (decodeRow 41 code)
  | .branch _ left right => .branch [] left.erase right.erase

def Tree.rows : Tree → List (List ℕ)
  | .leaf _ code => [decodeRow 41 code]
  | .branch _ left right => left.rows++right.rows

def Tree.contains (key : ℕ) : Tree → Bool
  | .leaf value _ => key=value
  | .branch pivot left right => if key< pivot then left.contains key else right.contains key

def Tree.checkKeys : Tree → Bool
  | .leaf key code => key=keyOfCode 41 code
  | .branch _ left right => left.checkKeys && right.checkKeys

end ThreeBoundRelaxedPacked

end
end Sensitivity213981Formal


