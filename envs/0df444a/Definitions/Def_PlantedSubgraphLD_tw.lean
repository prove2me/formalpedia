-- Prove2me | Definitions.Def_PlantedSubgraphLD_tw
-- name    : PlantedSubgraphLD_tw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:47.098187+00:00
-- url     : https://prove2.me/theorems/b6b485b0-a1c1-40f8-8df7-0931f0f50cf1
-- title:
--   Treewidth $\mathrm{tw}(G)$
-- statement:
--   A **tree decomposition** of a graph $G$ is a tree $T$ whose nodes $x$ carry vertex sets (bags) $B_x\subseteq V(G)$ such that every vertex lies in some bag, both endpoints of every edge lie in a common bag, and for each vertex $v$ the nodes whose bags contain $v$ form a connected subtree. Its **width** is $\max_x|B_x|-1$, and the **treewidth** $\mathrm{tw}(G)$ is the minimum width over all tree decompositions of $G$.
--
--   Treewidth measures how far a graph is from a tree (forests have treewidth at most $1$); a graph of small treewidth can be cut repeatedly along small vertex interfaces, which is what the decomposition argument of the paper uses.
--
--   **Formalization Note** $\mathrm{tw}(G)=\inf\{w:\ \mathrm{TreewidthLE}\ G\ w\}$, with the published `RobertsonSeymour1986.GM5.TreewidthLE` (a tree decomposition on a finite tree with all bags of size at most $w+1$). For a finite graph the set is nonempty (one bag holding every vertex), so the infimum is attained and $\mathrm{tw}(G)\le k$ is equivalent to `TreewidthLE G k`.
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §1.1, p.3 (PDF p.5); Definition 5.2, pp.25–26 (PDF pp.27–28)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

namespace PlantedSubgraphLD

/-- The treewidth `tw(G)` of a graph: the minimum width of a tree decomposition.

Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection* (manuscript of
Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §1.1, p.3 and Definition 5.2, pp.25–26: "The
width of the decomposition (T, (Bx)x∈V(T)) is maxx |Bx| − 1. The treewidth tw(F) of F is the
minimum width among all tree decompositions of F."

**Formalization Note** `tw G := sInf {w | TreewidthLE G w}`, with the published
`RobertsonSeymour1986.GM5.TreewidthLE` (a tree decomposition on a finite tree with every bag of
size `≤ w + 1`). For a finite graph the set is nonempty (one bag holding every vertex), so the
infimum is attained and `tw G ≤ k ↔ TreewidthLE G k`. -/
noncomputable def tw {V : Type} [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  sInf {w : ℕ | RobertsonSeymour1986.GM5.TreewidthLE G w}

end PlantedSubgraphLD


