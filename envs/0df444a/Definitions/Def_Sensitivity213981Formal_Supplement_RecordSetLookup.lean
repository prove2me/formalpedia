-- Prove2me | Definitions.Def_Sensitivity213981Formal_Supplement_RecordSetLookup
-- name    : Sensitivity213981Formal_Supplement_RecordSetLookup
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T18:24:15.176513+00:00
-- url     : https://prove2.me/theorems/c143b257-43e3-45cc-9e69-fcea49af529d
-- title:
--   Supplement Record Set Lookup — sensitivity certificate definitions
-- statement:
--   The definitions for Record Set Lookup in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRecordLookup.recordFast`, `ThreeBoundRecordLookup.checkTypes`, `ThreeBoundRecordLookup.checkLength`, `ThreeBoundRecordLookup.checkChunk`, `ThreeBoundRecordLookup.lexLess`, `ThreeBoundRecordLookup.Tree.contains`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RecordSetLookup.lean, lines 1–97.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_RecordSetLookup
import Definitions.Def_Sensitivity213981Formal_Supplement_Q2Enumeration
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort

namespace Sensitivity213981Formal
section
/- A finite exact-row search tree. Search soundness does not assume that
   the tree is ordered: a successful search always matches an actual leaf. -/


set_option autoImplicit false

namespace ThreeBoundRecordLookup



def lexLess : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _::_ => true
  | _::_, [] => false
  | a::as, b::bs => if a=b then lexLess as bs else a< b



def Tree.contains (row : List ℕ) : Tree → Bool
  | .leaf entry => decide (row=entry)
  | .branch pivot left right =>
      if lexLess row pivot then left.contains row else right.contains row



/-- Structurally recursive insertion sort gives a kernel-reducible version
    of the exact record; the standard merge-sort equality proves the match. -/
def recordFast (c : List ThreeBoundQ2.Kind × List Bool) : List ℕ := Id.run do
  let ts := c.1
  let vs := List.finRange ts.length
  let es := ThreeBoundQ2.edges ts.length
  let dirs := ThreeBoundQ2.directedEdges es c.2
  let residual := fun v : Fin ts.length =>
    ThreeBoundQ2.budget (ts.get v) - ThreeBoundQ2.outCount es c.2 v
  let incoming := fun v : Fin ts.length =>
    (dirs.filter fun e => ThreeBoundQ2.isGuard (ts.get e.1) && decide (e.2 = v)).length
  let typeCounts := (List.finRange 8).map fun t => (ts.filter fun u => u = t).length
  let external := ((vs.filter fun v => ThreeBoundQ2.isGuard (ts.get v)).map residual).sum
  let histogram := (List.finRange 8).flatMap fun t => [1,2].map fun h =>
    (vs.filter fun v => ts.get v = t ∧ min 2 (incoming v) = h).length
  let residuals := (vs.map residual).insertionSort (· ≤  ·)
  let prefixes := [1,2,3,4].map fun k =>
    if k ≤  ts.length then (residuals.take k).sum else 1000000
  return typeCounts ++ [external] ++ histogram ++ prefixes



def checkTypes (tree : Tree) (ts : List ThreeBoundQ2.Kind) : Bool :=
  (ThreeBoundQ2.casesFor ts).all fun c => tree.contains (recordFast c)

def checkLength (tree : Tree) (n : ℕ) : Bool :=
  (ThreeBoundQ2.typeLists 0 n).all (checkTypes tree)

def checkChunk (tree : Tree) (n start count : ℕ) : Bool :=
  (((ThreeBoundQ2.typeLists 0 n).drop start).take count).all (checkTypes tree)







end ThreeBoundRecordLookup



end
end Sensitivity213981Formal


