-- Prove2me | Definitions.Def_GnpColoring_inducedEdgeCount
-- name    : GnpColoring_inducedEdgeCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:30.226206+00:00
-- url     : https://prove2.me/theorems/ccaf2023-5e39-46e9-a241-9b8ec778c88b
-- title:
--   The number of edges of $G[B]$
-- statement:
--   For a vertex set $B$, the number of edges of the induced subgraph $G[B]$, i.e. the number of unordered pairs $\{u,w\}\subseteq B$ with $u\sim w$ in $G$.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Definition 3.2, p.15

import Mathlib

open scoped Classical
open Finset

namespace GnpColoring

/-- **The number of edges of `G[B]`**: the unordered pairs `{u, w} ⊆ B` with `u ~ w` in `G`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Definition 3.2, p.15 ("Every block B ∈ 𝓑 induces a tree with at most one extra edge").

**Formalization Note** Unordered pairs are counted as ordered pairs `(u, w)` with `u < w`. -/
noncomputable def inducedEdgeCount {n : ℕ} (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) : ℕ :=
  ((B ×ˢ B).filter fun p => p.1 < p.2 ∧ G.Adj p.1 p.2).card

end GnpColoring


