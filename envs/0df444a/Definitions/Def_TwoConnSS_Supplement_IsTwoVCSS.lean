-- Prove2me | Definitions.Def_TwoConnSS_Supplement_IsTwoVCSS
-- name    : TwoConnSS_Supplement_IsTwoVCSS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:45:00.161769+00:00
-- url     : https://prove2.me/theorems/872e6061-70d5-4631-87fe-9a0dcb7cc81a
-- title:
--   2-vertex-connected graphs and feasible 2VCSS solutions
-- statement:
--   A graph $H$ is **2-vertex-connected (2VC)** if it has at least three vertices and deleting any one vertex leaves it connected. This is the published notion of an $n$-tuply connected graph with $n=2$: at least $3$ vertices, and for every set $X$ of fewer than two vertices the graph $H-X$ is connected.
--
--   Let $G=(V,E)$ be a finite simple graph. A **2VCSS** of $G$ is an edge set $F\subseteq E$ such that the spanning subgraph $(V,F)$ is 2-vertex-connected. The **minimum 2-vertex-connected spanning subgraph problem (2VCSS)** asks, for a 2VC graph $G$, for a 2VCSS of $G$ with the fewest edges; its optimum is written $\mathrm{opt}_V(G)$.
--
--   These are the feasibility notions of Theorems 5.2 and 5.4.
--
--   **Formalization Note** The spanning subgraph of $F$ is the published `TwoConnSS.sg F`. The case $X=\emptyset$ (connectivity of $H$) of the published definition follows from the single-vertex cases once $H$ has three vertices, so it adds no condition. The optimum is never written as an infimum: statements compare with every 2VCSS $F'$.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a895e1fa238a27dca51f52b9f9f0c99a02bea4adcddcacca2e27e2ae6a), §5, p.18 (PDF 19); §6, p.23 (PDF 24)

import Mathlib
import Definitions.Def_Balinski61_Connectivity_TuplyConnected
import Definitions.Def_TwoConnSS_IsTwoECSS

namespace TwoConnSS.Supplement

/-- **2-vertex-connected graph.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §6, p.23: "A graph is … 2-vertex-
connected (2VC) if it has at least three vertices and deleting any vertex leaves it connected."

**Formalization Note.** This is the published `Balinski61.Connectivity.IsNTuplyConnected H 2`: at
least `2 + 1 = 3` vertices, and for every vertex set `X` with fewer than two vertices (`X = ∅` or a
single vertex) the subgraph induced on the other vertices is connected. The case `X = ∅`
(connectivity of `H`) follows from the single-vertex cases when there are at least three vertices,
so no condition is added. -/
def IsTwoVC {V : Type*} (H : SimpleGraph V) : Prop :=
  Balinski61.Connectivity.IsNTuplyConnected H 2

/-- **A feasible solution of 2VCSS (a 2VCSS of `G`).**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §5, p.18: "The minimum
2-vertex-connected spanning subgraph problem (2VCSS) imposes the analogous requirement for the
deletion of any one vertex"; §6, p.23: "We identify an edge set S ⊆ E(G) with the spanning
subgraph (V(G), S)".

`IsTwoVCSS G F` says `F ⊆ E(G)` and the spanning subgraph `(V, F)` (published `TwoConnSS.sg`) is
2-vertex-connected.

**Formalization Note.** The optimum `opt_V(G)` is never written as an infimum: every statement
compares with "every `F'` with `IsTwoVCSS G F'`". -/
def IsTwoVCSS {V : Type*} (G : SimpleGraph V) (F : Finset (Sym2 V)) : Prop :=
  (F : Set (Sym2 V)) ⊆ G.edgeSet ∧ IsTwoVC (TwoConnSS.sg F)

end TwoConnSS.Supplement


