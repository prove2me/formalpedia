-- Prove2me | Definitions.Def_HeilmanMax3Cut_Supplement_rankCutVal
-- name    : HeilmanMax3Cut_Supplement_rankCutVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:03:39.744839+00:00
-- url     : https://prove2.me/theorems/46a60a72-1666-45a6-89d3-58fc636bd54c
-- title:
--   The rank-$k$ MAX-CUT value
-- statement:
--   For a weighted graph $G$ and $k\ge1$, the rank-$k$ MAX-CUT value is
--
--   $$\max_{v_1,\dots,v_n\in S^{k-1}}\ \sum_{\{i,j\}\in E}w_{ij}\,\frac{1-\langle v_i,v_j\rangle}{2},$$
--
--   the maximum over assignments of unit vectors of $\mathbb R^k$ to the vertices ([BOV14], [HNP+23]). For $k=1$ it is MAX-CUT; for $k=3$ it equals the product-state Quantum MAX-CUT value up to normalization.
--
--   **Formalization Note** The paper names the problem without restating it; this is the [BOV14]/[HNP+23] definition. Edge weights are natural-number multiplicities in an edge list.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Theorem 1.8, p.6 (problem of [BOV14], [HNP+23])

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
open OptInapprox.MaxCut

namespace HeilmanMax3Cut.Supplement

/-- **The rank-`k` MAX-CUT value.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Theorem 1.8, p.6 ("the rank-`k` MAX-CUT problem"), the problem
of [BOV14] and [HNP+23]: for a weighted graph, maximize `∑_{\{i,j\} ∈ E} w_{ij} (1 − ⟨vᵢ, vⱼ⟩)/2` over
assignments of unit vectors `v₁, …, v_n ∈ S^{k−1} ⊂ ℝᵏ` to the vertices. For `k = 1` it is MAX-CUT;
`α_BOV,k` of (6) is the approximation ratio of its rank-`k` Gaussian rounding.

**Formalization Note.** The paper names the problem without restating it; the definition is the
[BOV14]/[HNP+23] one. The instance is the published `OptInapprox.MaxCut.WMaxCut` (an edge listed
`m` times has weight `m`), so the sum runs over the edge list. `ℝᵏ` is `EuclideanSpace ℝ (Fin k)`.
The maximum is the real `sSup` of the image of a compact set, attained, and nonempty for `k ≥ 1`
(the theorems use `k ≥ 3`). -/
noncomputable def rankCutVal (k : ℕ) (G : WMaxCut) : ℝ :=
  sSup ((fun v : Fin G.n → EuclideanSpace ℝ (Fin k) =>
      (G.edges.map fun e => (1 - inner ℝ (v e.1) (v e.2)) / 2).sum) ''
    {v | ∀ i, ‖v i‖ = 1})

end HeilmanMax3Cut.Supplement


