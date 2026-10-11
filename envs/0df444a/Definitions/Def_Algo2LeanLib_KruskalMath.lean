-- Prove2me | Definitions.Def_Algo2LeanLib_KruskalMath
-- name    : Algo2LeanLib_KruskalMath
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:39:00.231153+00:00
-- url     : https://prove2.me/theorems/bec1da99-501f-45d0-ba4c-b5e300bdac44
-- title:
--   Kruskal mathematical graph and minimum spanning forest definitions
-- statement:
--   `Algo2Lean.Kruskal.Edge` carries an edge identifier, two integer endpoints and an integer weight. `Connected` is undirected reachability. `Forest` excludes adding an edge whose endpoints are already connected by the remaining edges. `Spans` requires input-edge membership and preservation of input connectivity. **`MinimumSpanningForest input selected`** means that `selected` is a spanning forest with weight no greater than every other spanning forest of `input`.
--
--   `Sorted` allows equal weights. `Scan pending selected result` processes the pending list, accepting precisely those edges whose endpoints are not yet connected. This abstraction is independent of union-find, heaps and generated program states. Negative weights, parallel edges and loops are allowed in input; the forest condition prevents retaining cycles or loops. The exchange and minimum-spanning-forest proofs are separate theorem nodes.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/KruskalMath.lean

import Std

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Finite undirected graph mathematics for Kruskal's algorithm. Edge identities
separate parallel input occurrences. Endpoints and weights are integers; weights
may be negative. This module does not depend on a union-find implementation or
on generated algorithm definitions.
-/

namespace Algo2Lean.Kruskal

structure Edge where
  id : Nat
  source : Int
  target : Int
  weight : Int
  deriving DecidableEq, Repr

/-- One undirected traversal of an edge present in the finite edge list. -/
def Adjacent (edges : List Edge) (u v : Int) : Prop :=
  ∃ edge ∈ edges, (edge.source = u ∧ edge.target = v) ∨
    (edge.source = v ∧ edge.target = u)

/-- Connectivity means existence of a finite undirected walk. -/
inductive Connected (edges : List Edge) : Int → Int → Prop where
  | refl (vertex : Int) : Connected edges vertex vertex
  | step {u v w : Int} : Adjacent edges u v → Connected edges v w → Connected edges u w













@[simp] theorem connected_nil {u v : Int} : Connected [] u v ↔ u = v := by
  constructor
  · intro path
    cases path with
    | refl => rfl
    | step edge _ => obtain ⟨e, member, _⟩ := edge; simp at member
  · intro same; subst v; exact .refl _





/-- An undirected forest is constructed by joining disconnected components.
    List order records an insertion order; no edge joins vertices already linked
    by the remaining edges. Loops and repeated input occurrences are excluded. -/
def Forest : List Edge → Prop
  | [] => True
  | edge :: rest => Forest rest ∧ ¬ Connected rest edge.source edge.target

/-- All selected edges come from the input and preserve exactly its connectivity. -/
structure Spans (input selected : List Edge) : Prop where
  subset : ∀ edge ∈ selected, edge ∈ input
  connected : ∀ u v, Connected input u v → Connected selected u v

/-- Total mathematical weight counts each selected occurrence once. -/
def weight (edges : List Edge) : Int := (edges.map Edge.weight).sum

/-- Minimum weight is compared against every spanning forest of the same input. -/
def MinimumSpanningForest (input selected : List Edge) : Prop :=
  Forest selected ∧ Spans input selected ∧
    ∀ other, Forest other → Spans input other → weight selected ≤ weight other

/-- Input edges may be parallel, looped, or negatively weighted. Distinct ids
    identify occurrences independently of endpoint and weight equality. -/
structure ValidInput (size : Nat) (edges : List Edge) : Prop where
  identities : (edges.map Edge.id).Nodup
  source : ∀ edge ∈ edges, 0 ≤ edge.source ∧ edge.source < size
  target : ∀ edge ∈ edges, 0 ≤ edge.target ∧ edge.target < size

/-- Edges are scanned in nondecreasing weight order. Equal weights are allowed. -/
def Sorted (edges : List Edge) : Prop :=
  edges.Pairwise (fun before after => before.weight ≤ after.weight)

/-- The mathematical scan keeps an edge exactly when it joins two current
    components. A union-find implementation only needs to realize this test. -/
inductive Scan : List Edge → List Edge → List Edge → Prop where
  | done (selected : List Edge) : Scan [] selected selected
  | reject {edge : Edge} {pending selected result : List Edge} :
      Connected selected edge.source edge.target → Scan pending selected result →
      Scan (edge :: pending) selected result
  | accept {edge : Edge} {pending selected result : List Edge} :
      ¬ Connected selected edge.source edge.target → Scan pending (edge :: selected) result →
      Scan (edge :: pending) selected result














/-- Adding one edge merges its two components and changes no other component. -/
def Joined (edges : List Edge) (a b u v : Int) : Prop :=
  Connected edges u v ∨
    (Connected edges u a ∧ Connected edges b v) ∨
    (Connected edges u b ∧ Connected edges a v)

























@[simp] theorem weight_nil : weight [] = 0 := rfl
@[simp] theorem weight_cons (edge : Edge) (edges : List Edge) :
    weight (edge :: edges) = edge.weight + weight edges := by simp [weight]






































end Algo2Lean.Kruskal


