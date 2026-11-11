-- Prove2me | Definitions.Def_NodeStableProj_Main_Stability
-- name    : NodeStableProj_Main_Stability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:58:01.659994+00:00
-- url     : https://prove2.me/theorems/9bf589ea-9f21-47e9-a3db-513488516dbe
-- title:
--   (D, D̂)-projections and distributional node stability
-- statement:
--   A randomized graph algorithm $\mathcal P$ is represented by its output laws $\mathcal P(G)$, probability measures on graphs. Two laws $P,P'$ are **$(\varepsilon,\delta)$-indistinguishable**, $P\approx_{\varepsilon,\delta}P'$ (Definition 2.4, the published `PFRelease.Indist`), if for every event $Y$
--   $$P(Y)\le e^{\varepsilon}P'(Y)+\delta\quad\text{and}\quad P'(Y)\le e^{\varepsilon}P(Y)+\delta .$$
--
--   Given reals $0<D<\hat D$, $\mathcal P$ is a **$(D,\hat D)$-projection** (Definition 3.1) if for every graph $G$, with probability 1, $\mathcal P(G)$ is a $\hat D$-bounded spanning subgraph of $G$, and $\mathcal P(G)=G$ whenever $G$ is $D$-bounded.
--
--   $\mathcal P$ is **$(\varepsilon,\delta)$-distributionally node-stable** (Definition 3.2) if $\mathcal P(G)\approx_{\varepsilon,\delta}\mathcal P(G')_{-v^*}$ for every $G$ and every $G'$ obtained from $G$ by adding a node $v^*$ with arbitrary incident edges, where $\mathcal P(G')_{-v^*}$ is the law of the output with $v^*$ deleted. It is **$(\varepsilon,\delta)$-distributionally node-stable on $n$-node graphs** if $\mathcal P(G)_{-v^*}\approx_{\varepsilon,\delta}\mathcal P(G')_{-v^*}$ for every pair of fixed-vertex node-neighbouring $n$-node graphs with differing node $v^*$.
--
--   **Formalization Note.** Laws are `Measure Graph`; deletion of $v^*$ is the pushforward under `Graph.deleteVertex`. The common vertex set of the fixed-vertex variant is any $n$-element set of labels (the paper identifies it with $[n]$).
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 10, Definitions 2.4, 3.1 and 3.2

import Mathlib
import Definitions.Def_PFRelease_Indist
import Definitions.Def_NodeStableProj_Main_Graph

open MeasureTheory

namespace NodeStableProj.Main

/-!
# (D, D̂)-projections and distributional node stability

Aden-Ali, Sealfon, Smith, Steinke, Ullman, *Node Differential Privacy via Node-Stable Graph
Projections*, STOC 2027 submission (manuscript sha256 42f18565…), p. 10, Definitions 2.4, 3.1
and 3.2.

* A randomized graph algorithm is represented by its output law: `P : Graph → Measure Graph`.
* `(ε, δ)`-indistinguishability (Definition 2.4) is the published `PFRelease.Indist`: both
  inequalities, every measurable event; `Graph` has the σ-algebra `⊤`, so every event counts.
* `P(G')_{−v*}` is the pushforward of `P(G')` under vertex deletion.
-/

/-- Definition 3.1: for `0 < D < D̂`, `P` is a `(D, D̂)`-projection if for every graph `G`, with
probability 1, `P(G)` is a `D̂`-bounded subgraph of `G` with the same vertex set, and `P(G) = G`
whenever `G` is `D`-bounded. -/
def IsProjection (D Dhat : ℝ) (P : Graph → Measure Graph) : Prop :=
  0 < D ∧ D < Dhat ∧
    ∀ G : Graph, ∀ᵐ H ∂(P G),
      H.SpanningSubgraph G ∧ H.Bounded Dhat ∧ (G.Bounded D → H = G)

/-- Definition 3.2: `P` is `(ε, δ)`-distributionally node-stable if
`P(G) ≈_{ε,δ} P(G')_{−v*}` for every `G` and every `G'` obtained from `G` by adding a node `v*`
with arbitrary incident edges. -/
def IsDistNodeStable (P : Graph → Measure Graph) (ε δ : ℝ) : Prop :=
  ∀ (G G' : Graph) (vstar : ℕ), AddsNode G G' vstar →
    PFRelease.Indist (P G) ((P G').map (fun H => H.deleteVertex vstar)) ε δ

/-- Definition 3.2, fixed-vertex variant: `P` is `(ε, δ)`-distributionally node-stable on
`n`-node graphs if `P(G)_{−v*} ≈_{ε,δ} P(G')_{−v*}` for every pair of fixed-vertex
node-neighbouring `n`-node graphs `G, G'` with differing node `v*` (Definition 2.3).

**Formalization Note.** The common vertex set is any `n`-element set of labels (the paper
identifies it with `[n]`). -/
def IsDistNodeStableOn (n : ℕ) (P : Graph → Measure Graph) (ε δ : ℝ) : Prop :=
  ∀ (G G' : Graph) (vstar : ℕ), G.IsNNode n → FixedVertexNeighbors G G' vstar →
    PFRelease.Indist ((P G).map (fun H => H.deleteVertex vstar))
      ((P G').map (fun H => H.deleteVertex vstar)) ε δ

end NodeStableProj.Main


