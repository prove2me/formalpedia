-- Prove2me | Definitions.Def_GraphTensorCP_Supplement_completeMultipartiteGraph
-- name    : GraphTensorCP_Supplement_completeMultipartiteGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:22:47.0832+00:00
-- url     : https://prove2.me/theorems/574308f4-344c-433b-a0a4-f7d5d35dd030
-- title:
--   Complete multipartite graph $K_{s_1,\ldots,s_k}$ and partition imbalance $\delta(s_1,\ldots,s_k)$
-- statement:
--   For positive integers $s_1,\ldots,s_k$, the **complete multipartite graph** $K_{s_1,\ldots,s_k}$ has $k$ independent parts of those sizes and contains every edge joining vertices in different parts. Put $N=\sum_i s_i$. Its **partition imbalance** is
--
--   $$
--   \delta(s_1,\ldots,s_k)=\min_{S\subseteq[k]}\left|N-2\sum_{i\in S}s_i\right|.
--   $$
--
--   The imbalance measures how closely the parts can be divided into two groups of equal total size and appears in the exact maximum-cut formula.
--
--   **Formalization Note** Parts and vertices are 0-based. Mathlib’s complete multipartite graph on vertices $(i,v)$ is transported through a finite equivalence to `Fin (Σ i, s i)`. The absolute value in $\delta$ is computed in the integers before returning a natural number.
-- source:
--   Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Definition 6.8, p.61; Theorem 6.10, p.62

import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite

namespace GraphTensorCP

namespace Supplement

/-- The canonical equivalence from vertices `(part, position)` to `Fin (Σ_i s_i)`. -/
noncomputable def multipartiteVertexEquiv {k : ℕ} (s : Fin k → ℕ) :
    (Σ i : Fin k, Fin (s i)) ≃ Fin (∑ i, s i) :=
  Fintype.equivOfCardEq (by simp)

/-- The complete multipartite graph `K_{s₁,...,s_k}` with positive part sizes `s_i`
(Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*,
arXiv:2610.34273 (version of 2026-11-03), Definition 6.8, p.61).

**Formalization Note.** Mathlib's complete multipartite graph has vertices
`Σ i : Fin k, Fin (s i)` and adjacency exactly when the part indices differ. It is transported
along the canonical finite equivalence to the paper's consecutively labelled vertex set
`Fin (Σ_i s_i)`. Parts and vertices are 0-based. -/
noncomputable def completeMultipartiteGraph {k : ℕ} (s : Fin k → ℕ) :
    SimpleGraph (Fin (∑ i, s i)) :=
  (SimpleGraph.completeMultipartiteGraph (fun i : Fin k => Fin (s i))).map
    (multipartiteVertexEquiv s).toEmbedding

noncomputable instance completeMultipartiteGraph_decidableAdj {k : ℕ} (s : Fin k → ℕ) :
    DecidableRel (completeMultipartiteGraph s).Adj := Classical.decRel _

/-- The partition imbalance
`δ(s₁,...,s_k) = min_{S ⊆ [k]} |N - 2 Σ_{i∈S} s_i|`, where `N = Σ_i s_i`
(Zhou, arXiv:2610.34273 (version of 2026-11-03), Theorem 6.10, p.62).

**Formalization Note.** The absolute value is computed in `ℤ` before returning a natural number;
the minimum ranges over every finite subset of the 0-based part index type. -/
noncomputable def partitionImbalance {k : ℕ} (s : Fin k → ℕ) : ℕ :=
  Finset.univ.inf' (by simp) fun S : Finset (Fin k) =>
    Int.natAbs ((∑ i, s i : ℕ) - 2 * (∑ i ∈ S, s i) : ℤ)

/-- Two or more positive parts contain at least two vertices. -/
theorem totalSize_gt_one {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hs : ∀ i, 0 < s i) : 1 < ∑ i, s i := by
  have hsum : ∑ _i : Fin k, 1 ≤ ∑ i, s i :=
    Finset.sum_le_sum fun i _ => hs i
  have hk' : 1 < ∑ _i : Fin k, 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  exact lt_of_lt_of_le hk' hsum

end Supplement

end GraphTensorCP


