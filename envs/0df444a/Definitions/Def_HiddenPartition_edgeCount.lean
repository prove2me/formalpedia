-- Prove2me | Definitions.Def_HiddenPartition_edgeCount
-- name    : HiddenPartition_edgeCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:26:26.089166+00:00
-- url     : https://prove2.me/theorems/137315b6-93d5-4d78-8573-677ff686c1c9
-- title:
--   Number of edges $|E(G[X])|$ of an induced subgraph
-- statement:
--   For a simple graph $G$ and a finite vertex set $X$, $\mathrm{edgeCount}(G,X)=|E(G[X])|$ is the number of edges of $G$ with both endpoints in $X$, each unordered edge counted once.
--
--   The **edge density** of a non-empty induced subgraph is $\mathrm{ED}(G[X])=|E(G[X])|/|X|$ (Section 2); the density bounds of Theorem 1.1 and Lemma 4.1 are stated with it.
-- source:
--   H. Agrawal, P. Eua-anant, B. Haeupler, B. Laekhanukit, P. Mihov, L. Milenković, R. Santos, Z. Zhang, From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering, STOC 2027 submission (manuscript sha256 17239d0bf911912040cb82c45ae979b179c419fb0b9e69d6d1413bf70068b601), §2 Graphs; Edge and Pair Densities, p.9 (pdf p.11)

import Mathlib

set_option autoImplicit false

open Classical

namespace HiddenPartition

/-- **Number of edges of an induced subgraph** (Agrawal et al., STOC 2027 submission,
manuscript sha256 17239d0b…, §2 "Graphs" and "Edge and Pair Densities", p.9 (pdf p.11)).

`edgeCount G X = |E(G[X])|`, the number of edges of `G` with both endpoints in `X`. Each edge
is an unordered pair and is counted once. The edge density of the paper is
`ED(G[X]) = |E(G[X])| / |X|`.

**Formalization Note.** `X.sym2` is the set of unordered pairs `{x, y}` with `x, y ∈ X`
(including the diagonal pairs `{x, x}`, which are never edges of a simple graph). Membership in
the edge set is decided classically. -/
noncomputable def edgeCount {V : Type*} [DecidableEq V] (G : SimpleGraph V) (X : Finset V) : ℕ :=
  (X.sym2.filter (fun e => e ∈ G.edgeSet)).card

end HiddenPartition


