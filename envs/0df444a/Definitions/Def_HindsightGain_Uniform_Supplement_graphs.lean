-- Prove2me | Definitions.Def_HindsightGain_Uniform_Supplement_graphs
-- name    : HindsightGain_Uniform_Supplement_graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:51:10.553266+00:00
-- url     : https://prove2.me/theorems/855bfbae-a6a6-4c69-a3d1-988cbb610024
-- title:
--   Edge counts, maximum cut, distance to bipartiteness, induced subgraphs
-- statement:
--   For a finite simple graph $G$, $e(G)$ is its number of edges, $v(G)$ its number of vertices and $\rho=e(G)/v(G)$. The **maximum cut** $\mathrm{mc}(G)$ is the largest number of edges with exactly one endpoint in $X$, over all vertex sets $X$, and the **distance to bipartiteness** is $\beta(G)=e(G)-\mathrm{mc}(G)$. For a vertex set $S$, $G[S]$ is the induced subgraph, and $\mathrm{mc}(G)/e(G)$ is the max-cut fraction.
--
--   For a sequence of graphs $G_N$ and retention probabilities $p_N$, with $H_N=G_N[S_{p_N}]$, the max-cut fraction is **preserved** if $\mathbb P(e(H_N)\ge1)\to1$ and, for every $\eta>0$,
--   $$\mathbb P\Big(e(H_N)\ge1\ \text{and}\ \Big|\tfrac{\mathrm{mc}(H_N)}{e(H_N)}-\tfrac{\mathrm{mc}(G_N)}{e(G_N)}\Big|\le\eta\Big)\to1 .$$
--
--   These are the graph quantities of Sections 1.3, 5.4 and 6.
--
--   **Formalization Note** The induced subgraph is kept on the whole vertex set with the vertices outside $S$ isolated; it has the same edges and cuts as $G[S]$. The fraction is used only on the event $e\ge1$, so no value is assigned to edgeless samples. Each $N$ uses its own sampling law; no coupling across $N$ is assumed.
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, pp.6-7, §5.4 p.26, §6 pp.26-28

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_subsets

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical Filter Topology

namespace HindsightGain.Uniform.Supplement

/-- The edges of a finite simple graph, each unordered edge once. -/
def edgeFinset' {V : Type} [Fintype V] (G : SimpleGraph V) : Finset (Sym2 V) :=
  (Finset.univ : Finset (Sym2 V)).filter (fun z => z ∈ G.edgeSet)

/-- `e(G)`, the number of edges. -/
def edgeCount {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ := (edgeFinset' G).card

/-- The number of edges with exactly one endpoint in `S` (each counted once, oriented from `S`). -/
def cutSize {V : Type} [Fintype V] (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ((S ×ˢ Sᶜ).filter (fun uv => G.Adj uv.1 uv.2)).card

/-- `mc(G)`, the maximum cut: the largest `cutSize` over all vertex subsets. -/
def maxCut {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (Finset.univ : Finset (Finset V)).sup (cutSize G)

/-- `β(G) := e(G) - mc(G)`, the distance to bipartiteness (p.6), as a real number. -/
def bipDist {V : Type} [Fintype V] (G : SimpleGraph V) : ℝ :=
  (edgeCount G : ℝ) - (maxCut G : ℝ)

/-- The induced subgraph `G[S]`, kept on the same vertex type with the vertices outside `S`
isolated; it has the same edges and cuts as `G[S]`. -/
def induced {V : Type} (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

/-- The max-cut fraction `mc(G)/e(G)`; it is used only where `e(G) ≥ 1`. -/
def cutFraction {V : Type} [Fintype V] (G : SimpleGraph V) : ℝ :=
  (maxCut G : ℝ) / (edgeCount G : ℝ)

/-- `ρ = e(G)/v(G)`. -/
def density {V : Type} [Fintype V] (G : SimpleGraph V) : ℝ :=
  (edgeCount G : ℝ) / (Fintype.card V : ℝ)

/-- The conclusion of Theorem 5 (p.7) for a sequence `G_N` on `Fin (n N)` and retention
probabilities `p N`: with probability tending to one `H_N = G_N[S_{p_N}]` has an edge, and
`mc(H_N)/e(H_N) - mc(G_N)/e(G_N) → 0` in probability (stated jointly with the edge event, so that
no ratio is assigned to an edgeless sample). Each `N` uses its own sampling law. -/
def CutFractionPreserved (n : ℕ → ℕ) (G : (N : ℕ) → SimpleGraph (Fin (n N))) (p : ℕ → ℝ) : Prop :=
  Tendsto (fun N => bernProb (fun _ : Fin (n N) => p N)
      (fun S => 1 ≤ edgeCount (induced (G N) S))) atTop (𝓝 1) ∧
  ∀ η : ℝ, 0 < η → Tendsto (fun N => bernProb (fun _ : Fin (n N) => p N)
      (fun S => 1 ≤ edgeCount (induced (G N) S) ∧
        |cutFraction (induced (G N) S) - cutFraction (G N)| ≤ η)) atTop (𝓝 1)

end HindsightGain.Uniform.Supplement


