-- Prove2me | Definitions.Def_Algo_prim_math_Analysis
-- name    : Algo_prim_math_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-11T01:08:33.752133+00:00
-- url     : https://prove2.me/theorems/90cb7e01-517c-478e-8112-c05fb45a4ed4
-- title:
--   Algo.prim.math.Analysis definitions
-- statement:
--   Definitions and required structural lemmas from `Algo.prim.math.Analysis`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/d832a5655d7cac6d032e728a4798128147b27922/examples/analysis/prim/math.lean

import Definitions.Def_Algo2LeanLib_KruskalMath_PrimExtension

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



/-!
The cut argument for Prim's minimum spanning tree algorithm. The graph and MST
definitions are shared with Kruskal: edge occurrences have identities, edges are
undirected, and weights are arbitrary integers. The proofs permit equal weights,
negative weights, loops, and parallel input occurrences.

`LightEdge` describes the only greedy choice required by Prim. `Safe.add_light`
shows that this choice preserves extendibility to a minimum spanning forest.
`Growth.minimum_spanning_tree` packages the complete mathematical argument;
an implementation proof only supplies the chosen cuts and final coverage.
-/

namespace Algo2Lean.Prim

open Algo2Lean.Kruskal

/-- An edge has one endpoint inside the cut and the other outside. -/
def Crosses (inside : Int → Prop) (edge : Edge) : Prop :=
  (inside edge.source ∧ ¬ inside edge.target) ∨
  (inside edge.target ∧ ¬ inside edge.source)

/-- An input edge has minimum weight among all edges crossing the given cut. -/
structure LightEdge (input : List Edge) (inside : Int → Prop) (edge : Edge) : Prop where
  member : edge ∈ input
  crosses : Crosses inside edge
  least : ∀ candidate ∈ input, Crosses inside candidate → edge.weight ≤ candidate.weight

/-- A cut respects the chosen edges when no chosen edge crosses it. -/
def Respects (inside : Int → Prop) (selected : List Edge) : Prop :=
  ∀ edge ∈ selected, ¬ Crosses inside edge







/-- Chosen edges are safe if every competing spanning forest can be replaced by
one containing them without increasing its weight. This definition does not
assume beforehand that a minimum spanning forest has been constructed. -/
def Safe (input selected : List Edge) : Prop :=
  ∀ other, Forest other → Spans input other →
    ∃ completion, Forest completion ∧ Spans input completion ∧
      (∀ edge ∈ selected, edge ∈ completion) ∧ weight completion ≤ weight other

















-- Main result: Correctness


/-- The mathematical loop invariant after the root has been selected. Chosen
edges form a safe tree connecting precisely the currently visited vertices.
The representation of the visited predicate is left to the implementation. -/
structure TreeState (input : List Edge) (root : Int) (visited : Int → Prop)
    (selected : List Edge) : Prop where
  root_visited : visited root
  subset : ∀ edge ∈ selected, edge ∈ input
  endpoints : ∀ edge ∈ selected, visited edge.source ∧ visited edge.target
  reaches : ∀ vertex, visited vertex → Connected selected root vertex
  forest : Forest selected
  safe : Safe input selected



















/-- A finite adjacency scan keeps the best known incoming edge at each unvisited
vertex. A negative parent means that no scanned edge reaches that vertex.
`processed` describes exactly the edges whose relaxations have been performed. -/
structure Frontier (processed : Edge → Prop) (visited : Int → Prop)
    (key parent : Int → Int) : Prop where
  witness : ∀ vertex, ¬ visited vertex → 0 ≤ parent vertex →
    ∃ edge, processed edge ∧ edge.source = parent vertex ∧
      edge.target = vertex ∧ edge.weight = key vertex
  complete : ∀ edge, processed edge → ¬ visited edge.target → 0 ≤ parent edge.target
  least : ∀ edge, processed edge → ¬ visited edge.target → key edge.target ≤ edge.weight

/-- Functional notation for one sequence assignment. -/
def assign (values : Int → Int) (index value : Int) : Int → Int :=
  fun vertex => if vertex = index then value else values vertex













/-- The main-loop key invariant after all adjacency lists of visited vertices
have been scanned. Vertices are discovered exactly when the cut reaches them. -/
abbrev Keys (input : List Edge) (visited : Int → Prop) (key parent : Int → Int) : Prop :=
  Frontier (fun edge => edge ∈ input ∧ visited edge.source) visited key parent

/-- An undirected adjacency representation contains a reverse occurrence of
the same weight for every directed input occurrence. -/
def Symmetric (input : List Edge) : Prop :=
  ∀ edge ∈ input, ∃ reverse ∈ input,
    reverse.source = edge.target ∧ reverse.target = edge.source ∧ reverse.weight = edge.weight







/-- The pure effect of scanning one adjacency list. The four constructors match
the empty list, visited-target, unchanged-key, and improved-key branches. -/
inductive KeyScan (visited : Int → Prop) (source : Int) :
    List (Int × Int) → (Int → Int) → (Int → Int) → (Int → Int) → (Int → Int) → Prop where
  | done (key parent : Int → Int) : KeyScan visited source [] key parent key parent
  | skip {vertex cost : Int} {rest : List (Int × Int)} {key parent finalKey finalParent : Int → Int} :
      visited vertex → KeyScan visited source rest key parent finalKey finalParent →
      KeyScan visited source ((vertex, cost) :: rest) key parent finalKey finalParent
  | keep {vertex cost : Int} {rest : List (Int × Int)} {key parent finalKey finalParent : Int → Int} :
      ¬ visited vertex → 0 ≤ parent vertex → key vertex ≤ cost →
      KeyScan visited source rest key parent finalKey finalParent →
      KeyScan visited source ((vertex, cost) :: rest) key parent finalKey finalParent
  | improve {vertex cost : Int} {rest : List (Int × Int)} {key parent finalKey finalParent : Int → Int} :
      ¬ visited vertex → (parent vertex < 0 ∨ cost < key vertex) →
      KeyScan visited source rest (assign key vertex cost) (assign parent vertex source)
        finalKey finalParent →
      KeyScan visited source ((vertex, cost) :: rest) key parent finalKey finalParent















end Algo2Lean.Prim


