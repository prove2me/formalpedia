-- Prove2me | Definitions.Def_SnarkGen_CycleCover_IsKCDCEven
-- name    : SnarkGen_CycleCover_IsKCDCEven
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:17.829009+00:00
-- url     : https://prove2.me/theorems/1980b3e8-dc75-48f8-80b9-71b4eae127e0
-- title:
--   k-CDC as a k-multiset of even subgraphs (Section 5)
-- statement:
--   A **cycle double cover** (CDC) of a graph $G$ is a multiset of cycles such that each edge of $G$ lies in exactly two cycles. A CDC is a **$k$-CDC** if its cycles can be coloured with $k$ colours so that no two cycles sharing an edge get the same colour. Each colour class is then a union of edge-disjoint cycles, i.e. an even subgraph, and the paper notes that it is often convenient to see a $k$-CDC as a $k$-multiset of even subgraphs. That is the form used here.
--
--   A $k$-CDC of a finite simple graph $G$ is a family $D_0, D_1, \dots, D_{k-1}$ of edge sets such that
--
--   1. every $D_i$ is an even subgraph of $G$, and
--   2. every edge $e$ of $G$ lies in exactly two members of the family, counted with multiplicity:
--
--   $$\bigl|\{ i \in \{0,\dots,k-1\} : e \in D_i \}\bigr| = 2 .$$
--
--   Repeated and empty classes are allowed. Because a graph decomposes into edge-disjoint cycles exactly when it is even (§5, p. 15, a milestone of this mission), such a family is the same thing as a $k$-CDC of cycles: decompose each class into cycles and give them its colour, or conversely merge the cycles of each colour. Any CDC with $k$ cycles is in particular such a family, each cycle forming its own class.
--
--   **Formalization Note** The family is a function `Fin k → Finset (Sym2 V)`, not a `Finset` of edge sets, so that equal classes count twice.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, pp. 14–15, Section 5

import Mathlib
import Definitions.Def_SnarkGen_CycleCover_IsEvenEdgeSet

namespace SnarkGen.CycleCover

/-- arXiv:1206.6690v3, p. 15: a *k-CDC* of `G`, in the form "a k-multiset of even subgraphs":
a family `D 0, …, D (k-1)` of even subgraphs of `G` (colour classes; repetitions and empty
classes allowed) such that every edge of `G` lies in exactly two of them, counted with
multiplicity over the indices. -/
def IsKCDCEven {V : Type*} [DecidableEq V] (G : SimpleGraph V) (k : ℕ)
    (D : Fin k → Finset (Sym2 V)) : Prop :=
  (∀ i, IsEvenEdgeSet G (D i)) ∧
    ∀ e ∈ G.edgeSet, (Finset.univ.filter (fun i => e ∈ D i)).card = 2

end SnarkGen.CycleCover


