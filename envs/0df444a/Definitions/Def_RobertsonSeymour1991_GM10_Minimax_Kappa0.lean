-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Kappa0
-- name    : RobertsonSeymour1991_GM10_Minimax_Kappa0
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:44:38.196204+00:00
-- url     : https://prove2.me/theorems/b7eec735-7c63-43a1-9346-ac942f4572d8
-- title:
--   (4.3), proof, p. 165 — the connectivity function κ₀ of a hypergraph
-- statement:
--   Let $G$ be a hypergraph and $E=E(G)$. For $X\subseteq E$, $\kappa_0(X)$ is the number of vertices of $G$ incident both with an edge in $X$ and with an edge in $E-X$.
--
--   In the proof of (4.3) the paper fixes $k\ge\gamma(G)$ and uses the connectivity function $\kappa(X)=\kappa_0(X)-k$ with $\mathcal A=\{\{e\}:e\in E(G)\}$; with this choice, biases extending $\mathcal A$ correspond to tangles of order $k+1$ and exact tree-labellings over $\mathcal A$ to branch-decompositions of width $\le k$.
--
--   **Formalization Note** $\kappa_0$ is integer valued (the cardinality of a finite set of vertices, cast to $\mathbb Z$), so that $\kappa_0-k$ is a function into $\mathbb Z$ as §3 requires.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 165, proof of (4.3)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph

namespace RobertsonSeymour1991.GM10.Minimax

variable {V E : Type}

/-- p. 165 (proof of (4.3)): for `X ⊆ E(G)`, `κ₀(X)` is the number of vertices of `G` incident both with
an edge in `X` and with an edge in `E(G) − X`. -/
noncomputable def Hypergraph.kappa0 (G : Hypergraph V E) (X : Set E) : ℤ :=
  ({v : V | (∃ e ∈ X, G.inc e v) ∧ ∃ e ∉ X, G.inc e v}.ncard : ℤ)

end RobertsonSeymour1991.GM10.Minimax


