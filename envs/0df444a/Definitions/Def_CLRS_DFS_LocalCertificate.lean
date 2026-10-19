-- Prove2me | Definitions.Def_CLRS_DFS_LocalCertificate
-- name    : CLRS_DFS_LocalCertificate
-- status  : Definition
-- author  : @fizzyinc3
-- created : 2026-10-17T03:17:04.126283+00:00
-- url     : https://prove2.me/theorems/4759e3bb-941a-4df1-8aa8-320eec972056
-- title:
--   Local timestamp and label invariants for completed DFS
-- statement:
--   Let $G$ be a finite directed multigraph with $n$ vertices. Let $q,p,d,f,o,b$ denote the initial vertex priority, parent, discovery time, finish time, increasing finish order, and tree label, with $k$ tree labels.
--
--   The local certificate records timestamp and one-edge invariants of completed recursive DFS. Every vertex has $1\le d(v)<f(v)\le2n$; discovery times and finish times are separately injective, no discovery equals a finish, and the closed vertex intervals are nested or disjoint. Each vertex is either a root with parent $-1$, or has a parent edge whose interval strictly encloses its interval. Whenever $u$ strictly encloses $v$, the parent of $v$ is a vertex with interval inside that of $u$. Every edge satisfies
--   $$d(v)<f(u)\qquad(u\to v).$$
--
--   The certificate also records the original priority condition at each root, the permutation and increasing-finish properties of $o$, labels in $\{0,\ldots,k-1\}$ with every label attained, inheritance of labels across parent links, and agreement between label order and discovery order at roots. It assumes no parent-path, ancestry, white-path, or common-root characterization.
--
--   The accompanying local postcondition retains the generated DFS result object, six distinct fresh output arrays, preservation of all initial caller storage and other clocks, black colors, final event clock $2n$, finished count $n$, and tree count $k\le n$. It replaces only the global forest predicate by this local certificate. This interface separates the recursive program invariants from their graph-theoretic consequences.
-- source:
--   CLRS, Introduction to Algorithms, fourth edition, Section 20.3, DFS and DFS-VISIT, Theorems 20.7 and 20.9. Local invariant interface extracted for the existing Algo2Lean DFS program; supporting exposition: Jessica Su, Stanford CS 161 Lecture 10, Sections 2.3–2.4, PDF pages 7–9, https://web.stanford.edu/class/archive/cs/cs161/cs161.1168/lecture10-draft.pdf .

import Definitions.Def_CLRS_DFS_Program

set_option autoImplicit false

open Algo2LeanGenerated CLRS.GraphTraversal

namespace CLRS.DFS

/-- Local facts about completed recursive DFS. A nonroot parent strictly encloses
its child, and is inside every interval strictly enclosing that child. Every
edge has its target discovered before its source finishes. Tree labels are
inherited across parent links. No path or ancestry properties are assumed. -/
structure LocalCertificate (g : Graph)
    (inputOrder parent discover finish order component : Seq) (count : Nat) : Prop where
  times : ∀ v : Int, Vertex g v →
    1 ≤ discover v ∧ discover v < finish v ∧ finish v ≤ 2 * (g.size : Int)
  discoveryDistinct : ∀ u v : Int, Vertex g u → Vertex g v →
    discover u = discover v → u = v
  finishDistinct : ∀ u v : Int, Vertex g u → Vertex g v →
    finish u = finish v → u = v
  eventDistinct : ∀ u v : Int, Vertex g u → Vertex g v → discover u ≠ finish v
  parentheses : ∀ u v : Int, Vertex g u → Vertex g v →
    finish u < discover v ∨ finish v < discover u ∨
      (discover u ≤ discover v ∧ finish v ≤ finish u) ∨
      (discover v ≤ discover u ∧ finish u ≤ finish v)
  parentCases : ∀ v : Int, Vertex g v →
    parent v = -1 ∨
      Edge g (parent v) v ∧ discover (parent v) < discover v ∧ finish v < finish (parent v)
  parentNearest : ∀ u v : Int, Vertex g u → Vertex g v →
    discover u < discover v → finish v < finish u →
      Vertex g (parent v) ∧ discover u ≤ discover (parent v) ∧ finish (parent v) ≤ finish u
  edgeScanned : ∀ u v : Int, Edge g u v → discover v < finish u
  rootPriority : ∀ i : Nat, i < g.size →
    parent (inputOrder (i : Int)) = -1 → ∀ j : Nat, j < i →
      finish (inputOrder (j : Int)) < discover (inputOrder (i : Int))
  finishOrder : VertexOrder g order
  finishIncreasing : ∀ i j : Nat, i < j → j < g.size →
    finish (order (i : Int)) < finish (order (j : Int))
  componentRange : ∀ v : Int, Vertex g v →
    0 ≤ component v ∧ component v < (count : Int)
  componentCoverage : ∀ label : Nat, label < count →
    ∃ v : Int, Vertex g v ∧ component v = (label : Int)
  parentLabel : ∀ v : Int, Vertex g v → parent v ≠ -1 → component (parent v) = component v
  componentOrder : ∀ u v : Int, Vertex g u → Vertex g v →
    parent u = -1 → parent v = -1 →
    (component u < component v ↔ discover u < discover v)

/-- The storage and accounting part of the ordered DFS contract, exposing local
completed-call invariants instead of global ancestry and path equivalences. -/
def LocalPost (before after : Heap) (result : ObjectRef) (g : Graph)
    (inputOrder : Seq) : Prop :=
  Algo.dfs.Algo2LeanGenerated.is_DFSResult after result ∧
  FreshObject before after result ∧ Preserves before after ∧
  ∃ color parent discover finish order component : SeqRef,
    Algo.dfs.Algo2LeanGenerated.field_DFSResult_color after result = some color ∧
    Algo.dfs.Algo2LeanGenerated.field_DFSResult_parent after result = some parent ∧
    Algo.dfs.Algo2LeanGenerated.field_DFSResult_discover after result = some discover ∧
    Algo.dfs.Algo2LeanGenerated.field_DFSResult_finish after result = some finish ∧
    Algo.dfs.Algo2LeanGenerated.field_DFSResult_order after result = some order ∧
    Algo.dfs.Algo2LeanGenerated.field_DFSResult_component after result = some component ∧
    FreshArrays before after [color, parent, discover, finish, order, component] ∧
    Algo.dfs.Algo2LeanGenerated.field_DFSResult_clock after result = some (2 * (g.size : Int)) ∧
    Algo.dfs.Algo2LeanGenerated.field_DFSResult_finished after result = some (g.size : Int) ∧
    (∀ v : Int, Vertex g v → after.read color v = 2) ∧
    ∃ count : Nat,
      Algo.dfs.Algo2LeanGenerated.field_DFSResult_components after result = some (count : Int) ∧
      count ≤ g.size ∧
      LocalCertificate g inputOrder (after.read parent) (after.read discover)
        (after.read finish) (after.read order) (after.read component) count

end CLRS.DFS


