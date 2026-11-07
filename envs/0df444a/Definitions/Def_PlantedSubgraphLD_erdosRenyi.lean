-- Prove2me | Definitions.Def_PlantedSubgraphLD_erdosRenyi
-- name    : PlantedSubgraphLD_erdosRenyi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:58.137862+00:00
-- url     : https://prove2.me/theorems/60706a90-c6fd-4901-b89d-2224ff71fc79
-- title:
--   The Erdős–Rényi null law $Q_n=G(n,c/n)$
-- statement:
--   Fix $c>0$ and $n\ge 1$ and write $p=c/n$. The **null distribution** $Q_n=G(n,c/n)$ is the Erdős–Rényi random graph on the vertex set $[n]$: each of the $\binom n2$ unordered pairs of distinct vertices is an edge independently with probability $p$. The probability of a graph $G$ on $[n]$ with $e(G)$ edges is
--
--   $$
--   Q_n(G)=\prod_{1\le i<j\le n}\begin{cases}p&\{i,j\}\in E(G),\\ 1-p&\{i,j\}\notin E(G)\end{cases}\;=\;p^{e(G)}(1-p)^{\binom n2-e(G)} .
--   $$
--
--   It is the hypothesis $H_0$ of the testing problem and the reference measure of every $L^2(Q_n)$ norm in the paper.
--
--   **Formalization Note** Graphs on $[n]$ are `SimpleGraph (Fin n)` and a law is a real function on this finite type. The weight is the published `LPCommunity.SBMRecovery.edgeWeight` with edge probability $c/n$, which clamps the probability into $[0,1]$; for $n>c$ (the paper's standing assumption $0<c/n<1$, §3.1) the clamp changes nothing. All statements are about $n\to\infty$, so the values for $n\le c$ do not matter.
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §1.1, p.3 (PDF p.5); §3.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting

namespace PlantedSubgraphLD

/-- The null law `Qₙ = G(n, c/n)` (Erdős–Rényi graph with edge probability `c/n`).

Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §1.1, p.3 and §3.2, p.12:
"Fix c > 0, and let the null distribution be the Erdős–Rényi graph Qn = G(n, c/n)."

`erdosRenyi c n G` is the probability of the graph `G` on `[n]`, the product over the unordered
pairs `{i, j}` (`i < j`) of `c/n` if `{i, j}` is an edge of `G` and `1 − c/n` otherwise, i.e.
`(c/n)^{e(G)} (1 − c/n)^{C(n,2) − e(G)}`.

**Formalization Note** Outcomes are `SimpleGraph (Fin n)` (the paper's `{0,1}^{([n] choose 2)}`), and
a law is a real function on this finite type. The product weight is the published
`LPCommunity.SBMRecovery.edgeWeight`, which clamps the edge probability into `[0, 1]`; for
`n > c` (the paper's standing assumption "n is large enough that 0 < c/n < 1", §3.1, p.11) the
clamp is the identity. Every statement of the mission is about `n → ∞`, so the values for
`n ≤ c` do not matter. -/
noncomputable def erdosRenyi (c : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) : ℝ :=
  LPCommunity.SBMRecovery.edgeWeight G (fun _ _ => c / n)

end PlantedSubgraphLD


