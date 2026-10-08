-- Prove2me | Definitions.Def_SpectralSparsify_Sampling_Sample
-- name    : SpectralSparsify_Sampling_Sample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:05.564956+00:00
-- url     : https://prove2.me/theorems/2c999fdb-5514-4bb3-92b2-8599892fd153
-- title:
--   The procedure Sample((S, F), ε, p, λ) of Theorem 6.1: F = edges of G(S), H = E − F, Υ = (12k/(ελ))², and G̃ = (V, F̃ ∪ H)
-- statement:
--   Let $G=(V,E)$ be an unweighted graph and $S\subseteq V$. Let $F$ be the set of edges of the induced subgraph $G(S)$ (edges of $G$ with both endpoints in $S$), $H=E-F$ the rest of the edges, and for $i\in S$ let $d_i$ be the degree of $i$ in $G(S)$.
--
--   The procedure $\mathtt{Sample}((S,F),\epsilon,p,\lambda)$ (p. 8) sets
--   $$\Upsilon=\Big(\frac{12k}{\epsilon\lambda}\Big)^2,\qquad p_{i,j}=\min\Big(1,\frac{\Upsilon}{\min(d_i,d_j)}\Big)\quad\text{for every edge }(i,j)\in F,$$
--   and puts each edge $(i,j)$ of $F$, independently with probability $p_{i,j}$, into $\widetilde F$ with weight $1/p_{i,j}$. The graph of Theorem 6.1 is $\widetilde G=(V,\widetilde F\cup H)$: weight $1/p_{i,j}$ on the kept edges of $F$, weight $1$ on each edge of $H$, and no other edges.
--
--   In the paper step 1 of $\mathtt{Sample}$ sets $k=\max(\log_2(3/p),\log_2 n)$ with $n=|S|$, the number of vertices of its input graph $(S,F)$.
--
--   **Formalization Note** `k` is a natural-number parameter of `sampleUpsilon` and `sampleSubgraphProb`; Theorem 6.1 constrains it ($k$ even, $k\ge\log_2(3/p)$, $k\ge\log_2|S|$), because the paper's proof applies Lemma 6.3, which needs an even integer $k$. `inducedDegree G S i` counts the neighbours of $i$ in $S$, the degree of $i$ in $G(S)$ for $i\in S$. The probabilities use these $G(S)$-degrees, exactly as $\mathtt{Sample}$ does on its input $(S,F)$. `sparsifierWeight G S p T` is the weight function of $\widetilde G$ for the outcome $T\subseteq F$.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 8, Theorem 6.1 and the procedure Sample; §4, p. 4 (G(S))

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_EdgeSampling

namespace SpectralSparsify.Sampling

/-- `F`, the edges of the induced subgraph `G(S)` (Spielman–Teng, arXiv:0808.4134v3, §4, p. 4 and
Theorem 6.1, p. 8): the edges of `G` with both endpoints in `S` (`S.sym2` is the set of unordered
pairs with both entries in `S`). -/
def inducedEdges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset ∩ S.sym2

/-- `H = E - F`, the edges of `G` not in `G(S)` (Theorem 6.1, p. 8). -/
noncomputable def restEdges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset \ inducedEdges G S

/-- The degree of `i` in the induced subgraph `G(S)`, the number of neighbours of `i` lying in `S`
(meaningful for `i ∈ S`). -/
def inducedDegree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (i : V) : ℕ :=
  (G.neighborFinset i ∩ S).card

/-- Step 2 of `Sample` (p. 8): `Υ = (12k / (ελ))²` (`lam` is the paper's `λ`). -/
noncomputable def sampleUpsilon (k : ℕ) (ε lam : ℝ) : ℝ :=
  (12 * k / (ε * lam)) ^ 2

/-- Step 3 of `Sample((S, F), ε, p, λ)` (p. 8): the probability (4) of keeping the edge `{i, j}` of
`F`, computed with the degrees `d_i` of the input graph `G(S)` and `Υ = sampleUpsilon k ε λ`. -/
noncomputable def sampleSubgraphProb {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (k : ℕ) (ε lam : ℝ) : Sym2 V → ℝ :=
  sampleProb (fun v => (inducedDegree G S v : ℝ)) (sampleUpsilon k ε lam)

/-- The weight function of `G̃ = (V, F̃ ∪ H)` in Theorem 6.1 (p. 8) for the outcome `T ⊆ F` (the
edges kept by `Sample`): weight `1/p_{i,j}` on a kept edge of `F`, weight `1` on each edge of `H`,
and `0` elsewhere. -/
noncomputable def sparsifierWeight {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (p : Sym2 V → ℝ) (T : Finset (Sym2 V)) (u v : V) : ℝ :=
  if s(u, v) ∈ T then 1 / p s(u, v) else if s(u, v) ∈ restEdges G S then 1 else 0

end SpectralSparsify.Sampling


