-- Prove2me | Definitions.Def_BS2_b3ba934b_Q2Enumeration
-- name    : BS2_b3ba934b_Q2Enumeration
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:01:21.996229+00:00
-- url     : https://prove2.me/theorems/3e6873b1-48f1-46da-ac0b-b7ad84581cdb
-- title:
--   Sensitivity separation: Q2Enumeration (complete source module)
-- statement:
--   Complete Lean source module `Q2Enumeration` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Q2Enumeration.lean; original SHA-256 ae08990184d0a579a04d40716428c43f0aac40ead1b50813515c656180ffe56c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/-
An executable, exhaustive enumerator of the eight q <= 2 high-row types and
their budget-feasible tournament orientations.  The completeness proof is
structural, not an assertion that a foreign program enumerated all cases.

This module supplies finite combinatorial coverage.  It does not prove the
semantic charging inequalities for the sensitivity transfer.
-/
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort
import Lean.Elab.Tactic.Omega

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

theorem typeLists_complete (lo : Kind) (ts : List Kind)
    (hs : ts.Pairwise (· ≤ ·)) (hlo : ∀ t ∈ ts, lo ≤ t) :
    ts ∈ typeLists lo ts.length := by
  induction ts generalizing lo with
  | nil => simp [typeLists]
  | cons t ts ih =>
      obtain ⟨ht, hs⟩ := List.pairwise_cons.mp hs
      simp only [List.length_cons, typeLists]
      apply List.mem_flatMap.mpr
      refine ⟨t, List.mem_finRange t, ?_⟩
      rw [if_pos (hlo t (by simp))]
      exact List.mem_map.mpr ⟨ts, ih t hs ht, rfl⟩

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

theorem orientations_complete (es : List (V × V)) (ds : List Bool) (b : V → ℕ)
    (hlen : ds.length = es.length) (hb : ∀ v, outCount es ds v ≤ b v) :
    ds ∈ orientations b es := by
  induction es generalizing ds b with
  | nil =>
      have : ds = [] := List.length_eq_zero_iff.mp hlen
      subst ds
      simp [orientations]
  | cons e es ih =>
      cases ds with
      | nil => simp at hlen
      | cons d ds =>
          have hlen' : ds.length = es.length := by simpa using hlen
          cases d
          · have hpos : 0 < b e.1 := by
              have h := hb e.1
              simp only [outCount, Bool.false_eq_true, ↓reduceIte] at h
              omega
            have hrest : ∀ v, outCount es ds v ≤ spend b e.1 v := by
              intro v
              have h := hb v
              by_cases hv : v = e.1
              · subst v
                simp only [outCount, Bool.false_eq_true, ↓reduceIte] at h
                simp only [spend, ↓reduceIte]
                omega
              · have hv' : e.1 ≠ v := Ne.symm hv
                simpa [outCount, spend, hv, hv'] using h
            apply List.mem_append_left
            rw [if_pos hpos]
            exact List.mem_map.mpr ⟨ds, ih ds (spend b e.1) hlen' hrest, rfl⟩
          · have hpos : 0 < b e.2 := by
              have h := hb e.2
              simp only [outCount, ↓reduceIte] at h
              omega
            have hrest : ∀ v, outCount es ds v ≤ spend b e.2 v := by
              intro v
              have h := hb v
              by_cases hv : v = e.2
              · subst v
                simp only [outCount, ↓reduceIte] at h
                simp only [spend, ↓reduceIte]
                omega
              · have hv' : e.2 ≠ v := Ne.symm hv
                simpa [outCount, spend, hv, hv'] using h
            apply List.mem_append_right
            rw [if_pos hpos]
            exact List.mem_map.mpr ⟨ds, ih ds (spend b e.2) hlen' hrest, rfl⟩

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

/-- Every sorted typed tournament with at most seven vertices satisfying the
    stated necessary restrictions is included by the executable enumerator. -/
theorem allCases_complete (ts : List Kind) (ds : List Bool)
    (hn : ts.length ≤ 7) (hs : ts.Pairwise (· ≤ ·))
    (ht : allowedTypes ts) (hlen : ds.length = (edges ts.length).length)
    (hb : ∀ v : Fin ts.length,
      outCount (edges ts.length) ds v ≤ budget (ts.get v)) :
    (ts,ds) ∈ allCases := by
  apply List.mem_flatMap.mpr
  refine ⟨ts.length, List.mem_range.mpr (by omega), ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨ts, typeLists_complete 0 ts hs (fun t _ => Fin.zero_le _), ?_⟩
  rw [casesFor, if_pos ht]
  exact List.mem_map.mpr ⟨ds, orientations_complete _ _ _ hlen hb, rfl⟩

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

theorem records_complete (ts : List Kind) (ds : List Bool)
    (hn : ts.length ≤ 7) (hs : ts.Pairwise (· ≤ ·))
    (ht : allowedTypes ts) (hlen : ds.length = (edges ts.length).length)
    (hb : ∀ v : Fin ts.length,
      outCount (edges ts.length) ds v ≤ budget (ts.get v)) :
    record (ts,ds) ∈ records :=
  List.mem_map.mpr ⟨(ts,ds), allCases_complete ts ds hn hs ht hlen hb, rfl⟩

end ThreeBoundQ2

#print axioms ThreeBoundQ2.typeLists_complete
#print axioms ThreeBoundQ2.orientations_complete
#print axioms ThreeBoundQ2.records_complete


