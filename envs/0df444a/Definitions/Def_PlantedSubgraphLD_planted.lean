-- Prove2me | Definitions.Def_PlantedSubgraphLD_planted
-- name    : PlantedSubgraphLD_planted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:20:12.85965+00:00
-- url     : https://prove2.me/theorems/dd7a9408-8446-4a0a-85db-17c052185eec
-- title:
--   The planted law $P_n$
-- statement:
--   Let $\Gamma$ be a simple graph on a finite vertex set $V$ with $|V|\le n$ (the graph to be planted), and let $c>0$. The **planted distribution** $P_n$ is the law of the graph on $[n]$ obtained as follows: draw an injective map $\phi:V\to[n]$ uniformly at random, independently of a graph $G\sim G(n,c/n)$, and output the graph with edge set
--
--   $$
--   E(G)\cup\phi(E(\Gamma)),\qquad \phi(E(\Gamma))=\{\{\phi(u),\phi(v)\}:\{u,v\}\in E(\Gamma)\}.
--   $$
--
--   Equivalently, for a graph $G'$ on $[n]$,
--
--   $$
--   P_n(G')=\frac1{(n)_{|V|}}\sum_{\phi:V\hookrightarrow[n]}\ \sum_{G}Q_n(G)\,\mathbf 1\big[G\cup\phi(\Gamma)=G'\big],
--   $$
--
--   where $(n)_v=n(n-1)\cdots(n-v+1)$ is the number of injective maps. $P_n$ is the alternative $H_1$ before noise.
--
--   **Formalization Note** $\Gamma$ may have isolated vertices. If $|V|>n$ there is no injective map and the value is the junk $0$; the theorems assume $|V|\le n$.
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §1.1, p.3 (PDF p.5); §3.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_erdosRenyi

open Classical

namespace PlantedSubgraphLD

/-- The planted law `Pₙ`.

Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection* (manuscript of
Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.2, p.12: "Sample an injective map
ϕn : V(Γn) → [n] uniformly at random, independently of a graph G ∼ G(n, c/n), […] Then Pn is the
law of the graph with vertex set [n] and edge set E(G) ∪ ϕn(E(Γn))."

`planted c n Γ G'` is the probability of the graph `G'` on `[n]`:
`(1/(n)_{v(Γ)}) ∑_ϕ ∑_G Qₙ(G) · 1[G ∪ ϕ(Γ) = G']`, the sum over the injective maps `ϕ : V → [n]`
and the graphs `G` on `[n]`.

**Formalization Note** The planted graph `Γ` lives on a finite vertex type `V`; the theorems
assume `card V ≤ n`. Isolated vertices of `Γ` are allowed. `Γ.map ϕ` is the image graph
`ϕ(Γ)` and `⊔` the edge union. The normalization is `1 / card (V ↪ Fin n) = 1/(n)_{v}`; if
`card V > n` there is no injective map and the value is the junk `0`. -/
noncomputable def planted (c : ℝ) (n : ℕ) {V : Type} [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) (G' : SimpleGraph (Fin n)) : ℝ :=
  (1 / (Fintype.card (V ↪ Fin n) : ℝ)) *
    ∑ ϕ : V ↪ Fin n, ∑ G : SimpleGraph (Fin n),
      erdosRenyi c n G * (if G ⊔ Γ.map ϕ = G' then 1 else 0)

end PlantedSubgraphLD


