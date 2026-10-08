-- Prove2me | Definitions.Def_SpectralSparsify_Sampling_EdgeSampling
-- name    : SpectralSparsify_Sampling_EdgeSampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:09.674978+00:00
-- url     : https://prove2.me/theorems/0c7d985f-441b-49ae-a09d-8ffc7a8b961d
-- title:
--   The sampling probabilities (4) p_{i,j} = min(1, Υ/min(d_i, d_j)), the sampled graph G̃ with weights 1/p_{i,j}, and Δ = D^{-1}(Ã − A)
-- statement:
--   Let $G$ be an unweighted graph with degrees $d_i$ and let $\Upsilon>0$ be a parameter. The edge $\{i,j\}$ of $G$ is assigned the probability
--   $$p_{i,j}=\min\Big(1,\frac{\Upsilon}{\min(d_i,d_j)}\Big),\tag{4}$$
--   which is symmetric in $i,j$. Each edge is put in the sampled graph $\widetilde G$ independently with probability $p_{i,j}$, and a kept edge gets weight $1/p_{i,j}$. For an outcome $T$ (the set of kept edges), the adjacency matrix $\widetilde A$ of $\widetilde G$ has $\widetilde A_{i,j}=1/p_{i,j}$ if $\{i,j\}\in T$ and $0$ otherwise, so $\mathbf E[\widetilde A]=A$.
--
--   With $D$ the degree matrix and $A$ the adjacency matrix of $G$, the proof of Lemma 6.3 uses
--   $$\Delta=D^{-1}(\widetilde A-A).$$
--   For an edge $(i,j)$, $\Delta_{i,j}=\frac1{d_i}\big(\frac1{p_{i,j}}-1\big)$ with probability $p_{i,j}$ and $-\frac1{d_i}$ with probability $1-p_{i,j}$.
--
--   These are the random objects of Claim 6.5 and Lemmas 6.3, 6.4, 6.6 and 6.7.
--
--   **Formalization Note** `sampleProb d Υ` is defined on unordered pairs `Sym2 V`, which builds in $p_{i,j}=p_{j,i}$. `degSampleProb G Υ` uses `G.degree`. `sampledWeight p T` is the weight function of $\widetilde G$ for the outcome `T` (a set of edges of $G$); its weighted degrees, adjacency and degree matrices are `wDegree`, `adjMat`, `degMat` of the definition file of weighted graphs. `deltaMat` uses the diagonal matrix with entries `1 / d_v`, which is $D^{-1}$ when all degrees are positive (assumed wherever it is used).
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, §6, p. 7, (4); p. 9 (Ã); p. 10 (Δ)

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_WeightedGraph

namespace SpectralSparsify.Sampling

/-- The sampling probabilities (4) of Spielman–Teng, arXiv:0808.4134v3, §6, p. 7: for degrees `d`
and a parameter `Υ`, the edge `{i, j}` is kept with probability
`p_{i,j} = min(1, Υ / min(d_i, d_j))`. It is defined on unordered pairs, so `p_{i,j} = p_{j,i}`. -/
noncomputable def sampleProb {V : Type*} (d : V → ℝ) (Υ : ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun i j => min 1 (Υ / min (d i) (d j)), fun i j => by simp only [min_comm (d i) (d j)]⟩

/-- The probabilities (4) for the unweighted graph `G`, with `d_i` the degree of `i` in `G`. -/
noncomputable def degSampleProb {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Υ : ℝ) : Sym2 V → ℝ :=
  sampleProb (fun v => (G.degree v : ℝ)) Υ

/-- The weight function of the sampled graph `G̃` for the outcome `T` (the set of kept edges): an
edge `{u, v} ∈ T` gets weight `1 / p_{u,v}`, every other pair weight `0` (p. 7: "When edge `(i, j)`
is chosen to be in the graph, we multiply its weight by `1/p_{i,j}`"). Its weighted adjacency
matrix is `Ã`, with `Ã_{i,j} = 1/p_{i,j}` if the edge is kept and `0` otherwise (p. 9). -/
noncomputable def sampledWeight {V : Type*} [DecidableEq V] (p : Sym2 V → ℝ)
    (T : Finset (Sym2 V)) (u v : V) : ℝ :=
  if s(u, v) ∈ T then 1 / p s(u, v) else 0

/-- The matrix `Δ = D^{-1}(Ã - A)` of the proof of Lemma 6.3 (p. 10), where `D` is the degree matrix
of `G`, `A` its adjacency matrix and `Ã` the adjacency matrix of the sampled graph for the outcome
`T` and the probabilities `p`. -/
noncomputable def deltaMat {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : Sym2 V → ℝ) (T : Finset (Sym2 V)) : Matrix V V ℝ :=
  Matrix.diagonal (fun v => 1 / (G.degree v : ℝ)) *
    (adjMat (sampledWeight p T) - G.adjMatrix ℝ)

end SpectralSparsify.Sampling


