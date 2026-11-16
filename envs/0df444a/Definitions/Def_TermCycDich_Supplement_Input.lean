-- Prove2me | Definitions.Def_TermCycDich_Supplement_Input
-- name    : TermCycDich_Supplement_Input
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:49:17.976418+00:00
-- url     : https://prove2.me/theorems/a7b5285b-62dc-4da3-b69f-32aa630dcdb5
-- title:
--   Word-RAM inputs and verdicts for Terminal Cyclability with a tree-decomposition
-- statement:
--   Inputs of the treewidth algorithm of Theorem 1.4 on the published deterministic word RAM of `MinDegST.AddOne`:
--
--   1. an annotated graph $(G,R)$ on vertices $0,\dots,n-1$ is given by its adjacency lists (the number of vertices, the number $m$ of edges, and for every vertex its degree followed by its neighbours), followed by $|R|$ and the list of red vertices;
--   2. a tree-decomposition is appended as the number of bags, each bag as its size followed by its vertices, and the number of tree edges followed by the tree's edge list;
--   3. the output **verdict** is $[1]$ if $G$ has an $R$-cycle and $[0]$ otherwise.
--
--   These are the conventions under which a running time linear in $|G|$ is meaningful.
--
--   **Formalization Note** The paper names no machine or input format; adjacency lists are the standard input of linear-time graph algorithms.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 1.4, p.14 (PDF 16), restated p.63 (PDF 65)

import Mathlib
import Definitions.Def_MinDegST_AddOne_Machine
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition

open Classical

namespace TermCycDich

namespace Supplement

/-!
# Inputs and verdicts of the treewidth algorithm (Theorem 1.4) on the word RAM

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held
version, sha256 34a10f1a…4d4ea1), Theorem 1.4, p.14 (PDF 16), restated p.63 (PDF 65): "an
algorithm that takes as input an annotated graph (G, R) […] Moreover, if a tree-decomposition of
width at most k for G is supplied as part of the input […]".

The machine is the published deterministic word RAM of `MinDegST.AddOne` (programs of
`CongruencyTU.Program`, unit cost per instruction, no coins, no oracle, cost counter at halting,
`MinDegST.AddOne.HaltsWithin`, register bit length bounded by `MinDegST.AddOne.WordBounded`), and
the graph is given by adjacency lists (`MinDegST.AddOne.encAdj`).

* `tcInput n m adj rl`: the adjacency-list encoding of `G` (with `m` edges), followed by the red
  vertices: `|R|` and then the list `rl` of the red vertices.
* `treeOfEdges te`: the graph on `Fin nb` whose edges are the pairs listed in `te`.
* `tdInput n m adj rl nb bags te`: `tcInput` followed by a tree-decomposition: the number `nb` of
  bags, each bag as its size followed by its vertices, then the number of tree edges and the tree's
  edge list (as `MinDegST.AddOne.encPairs`).
* `verdict b`: the output `[1]` if `b` holds and `[0]` otherwise.

**Formalization Note** The paper names no machine model or input format. These are the standard
adjacency-list conventions of a linear-time graph algorithm; a linear running time is not
expressible on an adjacency-matrix or Turing-machine encoding.
-/

/-- Input: a graph by adjacency lists and the list of its red vertices. -/
def tcInput (n m : ℕ) (adj : Fin n → List (Fin n)) (rl : List (Fin n)) : List ℤ :=
  MinDegST.AddOne.encAdj n m adj ++ [(rl.length : ℤ)] ++ rl.map fun v => (v.val : ℤ)

/-- The tree on `Fin nb` whose edges are the listed pairs. -/
def treeOfEdges {nb : ℕ} (te : List (Fin nb × Fin nb)) : SimpleGraph (Fin nb) :=
  SimpleGraph.fromEdgeSet {e | ∃ p ∈ te, e = s(p.1, p.2)}

/-- Input: `tcInput` followed by a tree-decomposition with bags `bags` and tree edges `te`. -/
def tdInput (n m : ℕ) (adj : Fin n → List (Fin n)) (rl : List (Fin n)) (nb : ℕ)
    (bags : Fin nb → List (Fin n)) (te : List (Fin nb × Fin nb)) : List ℤ :=
  tcInput n m adj rl ++ [(nb : ℤ)] ++
    ((List.finRange nb).flatMap fun i => ((bags i).length : ℤ) :: (bags i).map fun v => (v.val : ℤ))
    ++ [(te.length : ℤ)] ++ MinDegST.AddOne.encPairs te

/-- The verdict output: `[1]` if `b` holds, `[0]` otherwise. -/
noncomputable def verdict (b : Prop) : List ℤ := if b then [1] else [0]

end Supplement

end TermCycDich


