-- Prove2me | Definitions.Def_Sensitivity213981Formal_Q3Enumeration
-- name    : Sensitivity213981Formal_Q3Enumeration
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:05:24.814733+00:00
-- url     : https://prove2.me/theorems/7c02eb02-af71-4f5e-b1f0-d0bb04067df7
-- title:
--   Q3 Enumeration — sensitivity certificate definitions
-- statement:
--   The definitions for Q3 Enumeration in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundQ3.allowedTypes`, `ThreeBoundQ3.instDecidableAllowedTypes`, `ThreeBoundQ3.casesFor`, `ThreeBoundQ3.allCases`, `ThreeBoundQ3.record`, `ThreeBoundQ3.Kind`, `ThreeBoundQ3.budget`, `ThreeBoundQ3.records`, `ThreeBoundQ3.isGuard`, `ThreeBoundQ3.positivePrefix`, `ThreeBoundQ3.orderKey`, `ThreeBoundQ3.typeLists`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Q3Enumeration.lean, lines 1–99.

import Definitions.Def_Sensitivity213981Formal_HighTypeCore
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
/- A complete executable eleven-type enumerator, with canonical budget order.
   The exact records retain all 41 coordinates used by the q3 transfer. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundQ3

abbrev Kind := ThreeBoundHighTypes.Kind 3
abbrev budget := ThreeBoundHighTypes.budget 3
abbrev isGuard := ThreeBoundHighTypes.isGuard 3
abbrev positivePrefix := ThreeBoundHighTypes.positivePrefix 3

export ThreeBoundQ2 (edges outCount orientations directedEdges orientationBits)

/-- Budget, then type number: exactly the stable order in the source generator. -/
def orderKey (k : Kind) : ℕ := 11*budget k+k.val

def typeLists (lo : ℕ) : ℕ → List (List Kind)
  | 0 => [[]]
  | n+1 => (List.finRange 11).flatMap fun t =>
      if lo≤ orderKey t then (typeLists (orderKey t) n).map (List.cons t) else []



/-- Every initial segment obeys its tournament edge budget, and every positive
    prefix obeys its own small-high-set bound. -/
def allowedTypes (ts : List Kind) : Prop :=
  (∀ k : Fin (ts.length+1), k.val*(k.val-1)/2≤ ((ts.take k.val).map budget).sum) ∧
  (∀ q : Fin 4, (ts.filter (positivePrefix q.val)).length≤ 2*q.val+1)

instance _root_.Sensitivity213981Formal.ThreeBoundQ3.instDecidableAllowedTypes (ts : List Kind) : Decidable (allowedTypes ts) := by
  unfold allowedTypes
  infer_instance

def casesFor (ts : List Kind) : List (List Kind×List Bool) :=
  if allowedTypes ts then
    (orientations (fun i : Fin ts.length => budget (ts.get i)) (edges ts.length)).map
      fun ds => (ts,ds)
  else []

def allCases : List (List Kind×List Bool) :=
  (List.range 10).flatMap fun n => (typeLists 0 n).flatMap casesFor



def record (c : List Kind×List Bool) : List ℕ := Id.run do
  let ts := c.1
  let vs := List.finRange ts.length
  let es := edges ts.length
  let dirs := directedEdges es c.2
  let residual := fun v : Fin ts.length => budget (ts.get v)-outCount es c.2 v
  let incoming := fun v : Fin ts.length =>
    (dirs.filter fun e => isGuard (ts.get e.1) && decide (e.2=v)).length
  let typeCounts := (List.finRange 11).map fun t => (ts.filter fun u => u=t).length
  let external := ((vs.filter fun v => isGuard (ts.get v)).map residual).sum
  let histogram := (List.finRange 11).flatMap fun t => [1,2].map fun h =>
    (vs.filter fun v => ts.get v=t ∧ min 2 (incoming v)=h).length
  let residuals := (vs.map residual).mergeSort (·≤ ·)
  let prefixes := [1,2,3,4,5,6,7].map fun k =>
    if k≤ ts.length then (residuals.take k).sum else 1000000
  return typeCounts++[external]++histogram++prefixes

def records : List (List ℕ) := allCases.map record



end ThreeBoundQ3



end
end Sensitivity213981Formal


