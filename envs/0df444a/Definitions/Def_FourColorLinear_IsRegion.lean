-- Prove2me | Definitions.Def_FourColorLinear_IsRegion
-- name    : FourColorLinear_IsRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:52.196203+00:00
-- url     : https://prove2.me/theorems/739dcf26-6058-4739-b488-8c98b441186e
-- title:
--   Regions, boundaries, holes, divisions and recursive $\vec r$-divisions
-- statement:
--   A **region** of a triangulation $G$ is a connected subgraph with at least one edge, carried by its edge set. A face of $G$ is an **inner face** of the region if all its edges are in the region; the other faces of the region are its **holes**. The **boundary** $\partial R$ consists of the edges and vertices around holes.
--
--   A **division** is a collection of regions such that every face of $G$ is an inner face of exactly one, and any edge shared by two regions is a boundary edge of each. An **$r$-division** has $O(n/r)$ regions, each with at most $r$ vertices, $O(\sqrt r)$ boundary vertices and a constant number of holes.
--
--   A **recursive division** is a rooted tree of regions, given by the number of regions per level, the parent of each region, and the edge list of each leaf, in which each node's region is the union of its descending leaves and each level is a division. A **recursive $\vec r$-division** has each level $i$ an $r_i$-division, and $O(r_i/r_{i-1})$ children per node.
--
--   **Formalization Note** The region count has $+1$: for $r>n$ one region is the only possibility.
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), §2, p.11

import Mathlib
import Definitions.Def_FourColorLinear_FaceOf

open PlanarQueue.Genus

namespace FourColorLinear

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A region (arXiv:2610.39753, held version, sha256 4dce39c5…, p.11): "a connected subgraph of G
with at least one edge". A connected subgraph with an edge is determined by its edge set, which
carries it here. -/
def IsRegion (G : SimpleGraph V) (E : Set (Sym2 V)) : Prop :=
  E ⊆ G.edgeSet ∧ E.Nonempty ∧
    ∀ x ∈ edgeVerts E, ∀ y ∈ edgeVerts E, (SimpleGraph.fromEdgeSet E).Reachable x y

/-- The dart `d` lies on an inner face of the region (p.11: "The faces of R are inner if they are
faces of G"): the whole face of `G` at `d` is bounded by edges of `E`. -/
def InnerDart (S : EmbeddingScheme G) (E : Set (Sym2 V)) (d : G.Dart) : Prop :=
  ∀ k : ℕ, ((faceNext S)^[k] d).edge ∈ E

/-- The boundary edges (p.11): the edges of the region around a hole. -/
def boundaryEdges (S : EmbeddingScheme G) (E : Set (Sym2 V)) : Set (Sym2 V) :=
  {e | e ∈ E ∧ ∃ d : G.Dart, d.edge = e ∧ ¬ InnerDart S E d}

/-- The boundary vertices (p.11), the vertices around a hole. -/
def boundaryVerts (S : EmbeddingScheme G) (E : Set (Sym2 V)) : Set V :=
  edgeVerts (boundaryEdges S E)

/-- The holes of a region (p.11): the faces of the subgraph that are not faces of `G`. -/
def holes (S : EmbeddingScheme G) (E : Set (Sym2 V)) : Set (FaceOf S E) :=
  {Φ | ∃ d, faceOf S E d = Φ ∧ ¬ InnerDart S E d}

/-- A division (p.11): "a collection of regions R1, …, Rk such that every face of G is an inner face
in exactly one region Ri. Moreover, it is required that if an edge is shared by two or more regions,
then it has to be a boundary edge (that is, on a hole) of any region containing it." -/
def IsDivision {k : ℕ} (S : EmbeddingScheme G) (Rs : Fin k → Set (Sym2 V)) : Prop :=
  (∀ i, IsRegion G (Rs i)) ∧ (∀ d : G.Dart, ∃! i, InnerDart S (Rs i) d) ∧
    ∀ i j, i ≠ j → ∀ e, e ∈ Rs i → e ∈ Rs j → e ∈ boundaryEdges S (Rs i)

/-- An `r`-division with constants (p.11): "a division with O(n/r) regions such that every region has
at most r vertices and at most O(√r) boundary vertices"; `H` bounds the holes, footnote 2, p.11.

**Formalization Note** The region count carries `+ 1`: for `r > n` one region is the only possibility
and `O(n/r)` would be below it. For `r ≤ n` the `+ 1` only moves the constant. -/
def IsRDivision {k : ℕ} (S : EmbeddingScheme G) (Rs : Fin k → Set (Sym2 V)) (r : ℕ)
    (Kr Kb : ℝ) (H : ℕ) : Prop :=
  IsDivision S Rs ∧ (k : ℝ) ≤ Kr * (Fintype.card V / r) + 1 ∧
    ∀ i, (edgeVerts (Rs i)).ncard ≤ r ∧
      ((boundaryVerts S (Rs i)).ncard : ℝ) ≤ Kb * Real.sqrt r ∧ (holes S (Rs i)).ncard ≤ H

/-- A recursive division as output data (p.11): the depth `h`, the number of regions per level, the
parent of each region, and the edge list of each leaf (level 0). -/
structure RecDiv (n : ℕ) where
  /-- the depth -/
  h : ℕ
  /-- regions on each level -/
  count : ℕ → ℕ
  /-- `par i j` is the parent, on level `i + 1`, of region `j` on level `i` -/
  par : ℕ → ℕ → ℕ
  /-- the edge list of each leaf -/
  leaf : ℕ → List (Fin n × Fin n)

namespace RecDiv

variable {n : ℕ}

/-- The ancestor on level `i` of leaf `j`. -/
def ancestor (D : RecDiv n) (j : ℕ) : ℕ → ℕ
  | 0 => j
  | i + 1 => D.par i (ancestor D j i)

/-- The region of a node (p.11): "the region of any node is the union of its descending leaves". -/
def region (D : RecDiv n) (i a : ℕ) : Set (Sym2 (Fin n)) :=
  {e | ∃ j < D.count 0, D.ancestor j i = a ∧ ∃ p ∈ D.leaf j, s(p.1, p.2) = e}

/-- The output words of a recursive division. -/
def encode (D : RecDiv n) : List ℕ :=
  D.h :: (List.range (D.h + 1)).flatMap (fun i => D.count i :: (List.range (D.count i)).map (D.par i))
    ++ (List.range (D.count 0)).flatMap fun j =>
      (D.leaf j).length :: (D.leaf j).flatMap fun p => [p.1.val, p.2.val]

/-- The tree shape: one root, parents in range, and every node has a child. -/
def IsTree (D : RecDiv n) : Prop :=
  D.count D.h = 1 ∧ ∀ i < D.h, (∀ j < D.count i, D.par i j < D.count (i + 1)) ∧
    ∀ a < D.count (i + 1), ∃ j < D.count i, D.par i j = a

/-- The children of node `a` on level `i + 1`. -/
def children (D : RecDiv n) (i a : ℕ) : Finset ℕ :=
  (Finset.range (D.count i)).filter fun j => D.par i j = a

end RecDiv

/-- A recursive division of the triangulation (p.11): a tree whose regions on each level form a
division of `G`. -/
def IsRecursiveDivision {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (S : EmbeddingScheme G) (D : RecDiv n) : Prop :=
  D.IsTree ∧ ∀ i ≤ D.h, IsDivision S fun a : Fin (D.count i) => D.region i a

/-- A recursive `r⃗`-division (p.11): "a recursive division where all leaves are at level 0 and where
the regions at level i form an ri-division of G. Moreover, regions on level i have O(ri/ri−1) children
on level i − 1." -/
def IsRecursiveRDivision {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (S : EmbeddingScheme G) (D : RecDiv n) (r : ℕ → ℕ) (Kr Kb Kc : ℝ) (H : ℕ) : Prop :=
  IsRecursiveDivision S D ∧
    (∀ i ≤ D.h, IsRDivision S (fun a : Fin (D.count i) => D.region i a) (r i) Kr Kb H) ∧
    ∀ i < D.h, ∀ a < D.count (i + 1),
      ((D.children i a).card : ℝ) ≤ Kc * ((r (i + 1) : ℝ) / r i)

end FourColorLinear


