-- Prove2me | Definitions.Def_Sensitivity213303_Q2Enumeration
-- name    : Sensitivity213303_Q2Enumeration
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T21:34:01.460502+00:00
-- url     : https://prove2.me/theorems/bb4581ca-caeb-4de4-983f-ed659f9c12de
-- title:
--   An exhaustive finite record model for high heads at tolerance at most two
-- statement:
--   The model has eight candidate kinds: three positive-only kinds, three pure-guard kinds, and two target–guard overlap kinds. Their outgoing budgets are [0,1,2,1,2,3,1,2]. It enumerates sorted kind lists of length at most seven and all tournament orientations within those budgets, subject to the total-edge and positive-prefix restrictions. Each orientation produces a 29-field record: eight kind counts, one external guard residual, sixteen incoming-guard histogram counts, and four smallest-residual prefix sums. These definitions specify the exact executable table whose completeness is proved separately.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module Q2Enumeration; source SHA256 ae08990184d0a579a04d40716428c43f0aac40ead1b50813515c656180ffe56c.

/-
An executable, exhaustive enumerator of the eight q <= 2 high-row types and
their budget-feasible tournament orientations.  The completeness proof is
structural, not an assertion that a foreign program enumerated all cases.

This module supplies finite combinatorial coverage.  It does not prove the
semantic charging inequalities for the sensitivity transfer.
-/
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort



set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundQ2

/-- P0, P1-only, P2-only, G0-only, G1-only, G2, H1, H2. -/
abbrev Kind := Fin 8

def budget (t : Kind) : ℕ :=
  match t.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | 6 => 1
  | _ => 2

def isGuard (t : Kind) : Bool := 3 ≤ t.val

def positiveLevel (t : Kind) : Option ℕ :=
  match t.val with
  | 0 => some 0
  | 1 => some 1
  | 2 => some 2
  | 6 => some 1
  | 7 => some 2
  | _ => none

def positivePrefix (q : ℕ) (t : Kind) : Bool :=
  match positiveLevel t with
  | some b => b ≤ q
  | none => false

/-- Enumerate type multisets by writing their type sequence in increasing order. -/
def typeLists (lo : Kind) : ℕ → List (List Kind)
  | 0 => [[]]
  | n+1 => (List.finRange 8).flatMap fun t =>
      if lo ≤ t then (typeLists t n).map (List.cons t) else []



section Orientations
variable {V : Type} [DecidableEq V]

def spend (b : V → ℕ) (v : V) : V → ℕ :=
  fun w => if w = v then b w - 1 else b w

/-- A false bit directs an edge from its first endpoint to its second. -/
def outCount : List (V × V) → List Bool → V → ℕ
  | [], _, _ => 0
  | _::_, [], _ => 0
  | e::es, d::ds, v =>
      (if (if d then e.2 else e.1) = v then 1 else 0) + outCount es ds v

/-- Prune a partial orientation exactly when it would exceed a vertex budget. -/
def orientations (b : V → ℕ) : List (V × V) → List (List Bool)
  | [] => [[]]
  | e::es =>
      (if 0 < b e.1 then (orientations (spend b e.1) es).map (List.cons false) else []) ++
      (if 0 < b e.2 then (orientations (spend b e.2) es).map (List.cons true) else [])



end Orientations

/-- Each unordered vertex pair occurs once, with the smaller index first. -/
def edges (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => i < j).map fun j => (i,j)

def allowedTypes (ts : List Kind) : Prop :=
  ts.length * (ts.length - 1) / 2 ≤ (ts.map budget).sum ∧
  (ts.filter (positivePrefix 0)).length ≤ 1 ∧
  (ts.filter (positivePrefix 1)).length ≤ 3 ∧
  (ts.filter (positivePrefix 2)).length ≤ 5

instance (ts : List Kind) : Decidable (allowedTypes ts) := by
  unfold allowedTypes
  infer_instance

def casesFor (ts : List Kind) : List (List Kind × List Bool) :=
  if allowedTypes ts then
    (orientations (fun i : Fin ts.length => budget (ts.get i)) (edges ts.length)).map
      fun ds => (ts, ds)
  else []

def allCases : List (List Kind × List Bool) :=
  (List.range 8).flatMap fun n => (typeLists 0 n).flatMap casesFor



def directedEdges {V : Type} (es : List (V × V)) (ds : List Bool) : List (V × V) :=
  (es.zip ds).map fun z => if z.2 then (z.1.2,z.1.1) else z.1

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
  let residuals := (vs.map residual).mergeSort (· ≤ ·)
  let prefixes := [1,2,3,4].map fun k =>
    if k ≤ ts.length then (residuals.take k).sum else 1000000
  return typeCounts ++ [external] ++ histogram ++ prefixes

/-- Executable full table, with duplicates retained; erasing duplicates is an
    optional representation optimization and cannot affect coverage. -/
def records : List (List ℕ) := allCases.map record



end ThreeBoundQ2


