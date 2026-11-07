-- Prove2me | Definitions.Def_SteinerNav_constructionEdges
-- name    : SteinerNav_constructionEdges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:46:53.483436+00:00
-- url     : https://prove2.me/theorems/a5161a2d-a492-4929-ad84-ec820d7c9521
-- title:
--   The three edge types of the construction of Theorem 3, and its type-3 edges
-- statement:
--   Let $P\subset\mathbb R^d$ be the input points, $Q\subseteq P$ a set of **landmarks** and $S$ a finite set of sampled locations, and let $R=S\setminus P$. The graph on $P\cup R$ has the following edges, always excluding self-loops:
--
--   1. an edge from each point of $R$ to each point of $P$;
--   2. an edge from each point of $P$ to each point of $Q\cup S$;
--   3. an edge from $s\in P$ to $t\in P\setminus\{s\}$ whenever
--   $$\|s-t\|<\min_{q\in Q}\|q-t\| .$$
--
--   The edges of the third kind are the **type-3 edges**. This is the graph of the proof of Theorem 3; its sparsity comes from reusing the landmarks' sampled neighbors for all sources.
--
--   **Formalization Note** The minimum over $Q$ is written as "for every $q\in Q$", which agrees with the page for nonempty $Q$; every theorem using it assumes $Q$ nonempty (the page has $m\ge1$ landmarks).
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), proof of Theorem 3, p.8 (edge types 1–3)

import Mathlib
import Definitions.Def_SteinerNav_Covers

namespace SteinerNav

open scoped Classical in
/-- The edges of type 3 for the landmark set `Q`: an edge from `s ∈ P` to `t ∈ P \ {s}` whenever
`‖s − t‖ < min_{q ∈ Q} ‖q − t‖` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), proof of Theorem 3, p.8).

**Formalization Note** The minimum is written as `∀ q ∈ Q`, so it agrees with the page only for
nonempty `Q`; every use assumes that (`m ≥ 1` on the page). -/
noncomputable def type3Edges {d : ℕ} (P Q : Finset (Pt d)) : Finset (Pt d × Pt d) :=
  (P ×ˢ P).filter fun e => e.1 ≠ e.2 ∧ ∀ q ∈ Q, dist e.1 e.2 < dist q e.2

open scoped Classical in
/-- The graph of the proof of Theorem 3 on `P ∪ R`, `R = S \ P`, for landmarks `Q` and sampled
locations `S`: (1) an edge from each point of `R` to each point of `P`; (2) an edge from each point
of `P` to each point of `Q ∪ S`; (3) the edges `type3Edges P Q`; always excluding self-loops
(Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), proof of Theorem 3, p.8). -/
noncomputable def constructionEdges {d : ℕ} (P Q S : Finset (Pt d)) : Finset (Pt d × Pt d) :=
  (((S \ P) ×ˢ P) ∪ (P ×ˢ (Q ∪ S)) ∪ type3Edges P Q).filter fun e => e.1 ≠ e.2

end SteinerNav


