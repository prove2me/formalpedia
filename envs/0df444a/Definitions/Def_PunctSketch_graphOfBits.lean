-- Prove2me | Definitions.Def_PunctSketch_graphOfBits
-- name    : PunctSketch_graphOfBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:42.38504+00:00
-- url     : https://prove2.me/theorems/a8755573-37e9-4f39-b1e5-726a5605652c
-- title:
--   Reading a graph and a vertex set from an output string
-- statement:
--   The coordinator's output is a bit string. This item reads a graph on $n$ vertices from $\binom n2$ bits, one for each pair $i<j$ in lexicographic order, and a vertex set from $n$ bits, one for each vertex.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §1, p.1 (PDF p.2)

import Mathlib

namespace PunctSketch

/-- The pairs `(i, j)` with `i < j`, in lexicographic order. There are `n.choose 2` of them. -/
def pairList (n : ℕ) : List (Fin n × Fin n) :=
  ((List.finRange n).product (List.finRange n)).filter (fun p => p.1 < p.2)

/-- **Reading a graph from an output bit string.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §1, p.1: the coordinator outputs "a small
k-connected spanning subgraph". Bit number `i` is the membership of the `i`-th pair of `pairList n`
in the edge set. -/
def graphOfBits {n : ℕ} (bits : List Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun x y => ((x, y), true) ∈ (pairList n).zip bits)

/-- **Reading a vertex set from an output bit string.** Vertex `v` belongs to it exactly when bit
number `v` is `true`. -/
def setOfBits {n : ℕ} (bits : List Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun v => bits[(v : ℕ)]? = some true)

end PunctSketch


