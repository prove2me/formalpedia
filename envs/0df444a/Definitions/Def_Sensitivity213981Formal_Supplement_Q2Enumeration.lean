-- Prove2me | Definitions.Def_Sensitivity213981Formal_Supplement_Q2Enumeration
-- name    : Sensitivity213981Formal_Supplement_Q2Enumeration
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T18:16:06.256186+00:00
-- url     : https://prove2.me/theorems/51c33a8b-a678-4cfe-a556-348ad8f4367f
-- title:
--   Supplement Q2 Enumeration — sensitivity certificate definitions
-- statement:
--   The definitions for Q2 Enumeration in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundQ2.typeLists`, `ThreeBoundQ2.casesFor`, `ThreeBoundQ2.allCases`, `ThreeBoundQ2.record`, `ThreeBoundQ2.records`, `ThreeBoundQ2.isGuard`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Q2Enumeration.lean, lines 1–214.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Q2Enumeration
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort

namespace Sensitivity213981Formal
section
/-
An executable, exhaustive enumerator of the eight q <= 2 high-row types and
their budget-feasible tournament orientations.  The completeness proof is
structural, not an assertion that a foreign program enumerated all cases.

This module supplies finite combinatorial coverage.  It does not prove the
semantic charging inequalities for the sensitivity transfer.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundQ2





def isGuard (t : Kind) : Bool := 3 ≤  t.val





/-- Enumerate type multisets by writing their type sequence in increasing order. -/
def typeLists (lo : Kind) : ℕ → List (List Kind)
  | 0 => [[]]
  | n+1 => (List.finRange 8).flatMap fun t =>
      if lo ≤  t then (typeLists t n).map (List.cons t) else []



section Orientations
variable {V : Type} [DecidableEq V]









end Orientations







def casesFor (ts : List Kind) : List (List Kind × List Bool) :=
  if allowedTypes ts then
    (orientations (fun i : Fin ts.length => budget (ts.get i)) (edges ts.length)).map
      fun ds => (ts, ds)
  else []

def allCases : List (List Kind × List Bool) :=
  (List.range 8).flatMap fun n => (typeLists 0 n).flatMap casesFor





def record (c : List Kind × List Bool) : List ℕ := Id.run do
  let ts := c.1
  let vs := List.finRange ts.length
  let es := edges ts.length
  let dirs := directedEdges es c.2
  let residual := fun v : Fin ts.length => budget (ts.get v) - outCount es c.2 v
  let incoming := fun v : Fin ts.length =>
    (dirs.filter fun e => isGuard (ts.get e.1) && decide (e.2 = v)).length
  let typeCounts := (List.finRange 8).map fun t => (ts.filter fun u => u = t).length
  let external := ((vs.filter fun v => isGuard (ts.get v)).map residual).sum
  let histogram := (List.finRange 8).flatMap fun t => [1,2].map fun h =>
    (vs.filter fun v => ts.get v = t ∧ min 2 (incoming v) = h).length
  let residuals := (vs.map residual).mergeSort (· ≤  ·)
  let prefixes := [1,2,3,4].map fun k =>
    if k ≤  ts.length then (residuals.take k).sum else 1000000
  return typeCounts ++ [external] ++ histogram ++ prefixes

/-- Executable full table, with duplicates retained; erasing duplicates is an
    optional representation optimization and cannot affect coverage. -/
def records : List (List ℕ) := allCases.map record



end ThreeBoundQ2





end
end Sensitivity213981Formal


