-- Prove2me | Definitions.Def_Sensitivity213303_RecordSetLookup
-- name    : Sensitivity213303_RecordSetLookup
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T21:55:53.776976+00:00
-- url     : https://prove2.me/theorems/7d93147d-5586-4db7-bb06-4c066cb5bc3b
-- title:
--   Exact record lookup and finite tournament-coverage checks
-- statement:
--   A binary tree stores exact natural-number record rows at its leaves and uses lexicographic pivots for lookup. A successful lookup compares against the complete leaf row. recordFast computes the same 29-field candidate record using insertion sort for its residual prefixes. checkTypes verifies every feasible orientation of one kind list against the tree; checkLength verifies every sorted kind list of a fixed length. These are the executable predicates used by the finite q≤2 coverage certificates.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module RecordSetLookup; source SHA256 8dce1a34ad70d9182b78e5469447addfc950e195435007566d76b111b592f4bc.

/- A finite exact-row search tree. Search soundness does not assume that
   the tree is ordered: a successful search always matches an actual leaf. -/
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort



set_option autoImplicit false

namespace ThreeBoundRecordLookup

inductive Tree where
  | leaf : List ℕ → Tree
  | branch : List ℕ → Tree → Tree → Tree

def lexLess : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _::_ => true
  | _::_, [] => false
  | a::as, b::bs => if a=b then lexLess as bs else a<b

def Tree.elements : Tree → List (List ℕ)
  | .leaf row => [row]
  | .branch _ left right => left.elements ++ right.elements

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
  let residuals := (vs.map residual).insertionSort (· ≤ ·)
  let prefixes := [1,2,3,4].map fun k =>
    if k ≤ ts.length then (residuals.take k).sum else 1000000
  return typeCounts ++ [external] ++ histogram ++ prefixes



def checkTypes (tree : Tree) (ts : List ThreeBoundQ2.Kind) : Bool :=
  (ThreeBoundQ2.casesFor ts).all fun c => tree.contains (recordFast c)

def checkLength (tree : Tree) (n : ℕ) : Bool :=
  (ThreeBoundQ2.typeLists 0 n).all (checkTypes tree)









end ThreeBoundRecordLookup


