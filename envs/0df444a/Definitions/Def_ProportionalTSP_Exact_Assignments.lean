-- Prove2me | Definitions.Def_ProportionalTSP_Exact_Assignments
-- name    : ProportionalTSP_Exact_Assignments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:28.301877+00:00
-- url     : https://prove2.me/theorems/20bb602e-2407-4dc2-96b2-be47aeada29e
-- title:
--   Assignments, generic cross costs, tight edges, and finite canonical minimizers
-- statement:
--   For parts $L$ and $R$ of sizes $m$ and $k$, an assignment is any map $A:R\to L$, its load is $d^A_l=|A^{-1}(l)|$, and its cost is
--   $$w(A)=\sum_{r\in R}w_{A(r)r}.$$
--   A feasible load has nonnegative integer entries summing to $k$; it is balanced when every entry is at most two. Genericity excludes zero alternating sums on every simple bipartite cycle. A tight edge minimizes $w_{lr}+a_l$ at its right endpoint, including ties and allowing arbitrary real prices.
--
--   The canonical-assignment specification scans all assignments in increasing base-$m$ rank, retains the first minimum, and has a declared fallback only for infeasible loads. This finite mathematical specification is not assigned a unit-time implementation; polynomial implementation is a theorem obligation. Uniqueness under genericity is not built into the definition.
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), Definitions 2.1–2.3 and Lemma 2.6, PDF p. 3–4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Tours

noncomputable section

namespace ProportionalTSP.Exact
open scoped BigOperators

abbrev Assignment (m k : ℕ) := Fin k → Fin m
abbrev Load (m : ℕ) := Fin m → ℕ

def load {m k : ℕ} (A : Assignment m k) : Load m :=
  fun l => (Finset.univ.filter (fun r => A r = l)).card

def feasible {m : ℕ} (k : ℕ) (d : Load m) : Prop := ∑ l, d l = k

def balanced {m : ℕ} (d : Load m) : Prop := ∀ l, d l ≤ 2

def assignmentCost {m k : ℕ} {K : Type} [AddCommMonoid K]
    (w : Fin m → Fin k → K) (A : Assignment m k) : K := ∑ r, w (A r) r

/-- The alternating sum ranges over distinct vertices in each part, length at least two. -/
def Generic {m k : ℕ} (w : Fin m → Fin k → ℝ) : Prop :=
  ∀ (t : ℕ) (_ht : 2 ≤ t) (ls : Fin t → Fin m) (rs : Fin t → Fin k),
    Function.Injective ls → Function.Injective rs →
      (∑ i : Fin t, (w (ls i) (rs i) - w (ls (finRotate t i)) (rs i))) ≠ 0

def TightEdge {m k : ℕ} (w : Fin m → Fin k → ℝ)
    (a : Fin m → ℝ) (S : Finset (Fin m)) (l : Fin m) (r : Fin k) : Prop :=
  l ∈ S ∧ ∀ j ∈ S, w l r + a l ≤ w j r + a j

def TightAssignment {m k : ℕ} (w : Fin m → Fin k → ℝ)
    (a : Fin m → ℝ) (A : Assignment m k) : Prop :=
  ∀ r, TightEdge w a Finset.univ (A r) r

def assignmentGraph {m k : ℕ} (A : Assignment m k) : SimpleGraph (Vertex m k) where
  Adj x y := match x, y with
    | .inl l, .inr r => A r = l
    | .inr r, .inl l => A r = l
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp_all⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

def tightGraph {m k : ℕ} (w : Fin m → Fin k → ℝ) (a : Fin m → ℝ) :
    SimpleGraph (Vertex m k) where
  Adj x y := match x, y with
    | .inl l, .inr r => TightEdge w a Finset.univ l r
    | .inr r, .inl l => TightEdge w a Finset.univ l r
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp_all⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

/-- Deterministic tie order: base-m digits in increasing R-index. -/
def assignmentRank {m k : ℕ} (A : Assignment m k) : ℕ := ∑ r, (A r).val * m ^ r.val

def assignmentList (m k : ℕ) : List (Assignment m k) :=
  (Finset.univ : Finset (Assignment m k)).toList.mergeSort
    (fun A B => decide (assignmentRank A ≤ assignmentRank B))

/-- A finite fold, retaining the first entry on ties. This is a specification, not a free oracle. -/
def argminList {X K : Type} (le : K → K → Prop) [DecidableRel le]
    (cost : X → K) (xs : List X) : Option X :=
  xs.foldl (fun best x => match best with
    | none => some x
    | some y => if le (cost y) (cost x) then some y else some x) none

def canonicalBy {m k : ℕ} [NeZero m] {K : Type} [AddCommMonoid K]
    (le : K → K → Prop) [DecidableRel le] (w : Fin m → Fin k → K) (d : Load m) : Assignment m k :=
  (argminList le (assignmentCost w) ((assignmentList m k).filter (fun A => decide (load A = d)))).getD
    (fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩)

def canonical {m k : ℕ} [NeZero m] (w : Fin m → Fin k → ℝ) (d : Load m) : Assignment m k :=
  canonicalBy (· ≤ ·) w d

def MinimumAssignment {m k : ℕ} (w : Fin m → Fin k → ℝ) (d : Load m)
    (A : Assignment m k) : Prop :=
  load A = d ∧ ∀ B, load B = d → assignmentCost w A ≤ assignmentCost w B

end ProportionalTSP.Exact


