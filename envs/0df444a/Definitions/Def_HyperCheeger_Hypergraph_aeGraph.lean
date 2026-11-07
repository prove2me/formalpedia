-- Prove2me | Definitions.Def_HyperCheeger_Hypergraph_aeGraph
-- name    : HyperCheeger_Hypergraph_aeGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:38.602929+00:00
-- url     : https://prove2.me/theorems/7f82119f-88c6-4686-bf9e-eeec412072dc
-- title:
--   The AE graph $G_H$ of a hypergraph
-- statement:
--   The **algebraically equivalent (AE) graph** $G_H$ of $H$ has the same vertices as $H$. Each hyperedge $e$ is replaced by a clique on its vertices with all edge weights $w_H(e)/(|e|-1)$, and parallel edges are merged by adding weights. So its edges are the 2-element subsets $p$ of hyperedges of $H$, with weight
--
--   $$w_{G_H}(p)=\sum_{e\in E_H:\,p\subseteq e}\frac{w_H(e)}{|e|-1}.$$
--
--   It is a weighted clique expansion of $H$, and it transfers the Cheeger inequality for 2-graphs to hypergraphs.
--
--   **Formalization Note.** A pair of total weight $0$ is still an edge, so $G_H$ stays connected when $H$ is.
-- source:
--   Kamal, Bagchi, A Cheeger Inequality for Hypergraphs and Its Applications, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), proof of Lemma 3.3, pp.9–10

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph

namespace HyperCheeger

namespace Hypergraph

variable {V : Type} [DecidableEq V]

/-- The **AE graph** `G_H` of `H` (proof of Lemma 3.3, pp.9–10), in the merged form the page allows:
same vertices; the edges are the 2-element subsets of the hyperedges of `H`; and the weight of `p` is the
sum of `w_H(e)/(|e|−1)` over the hyperedges `e ⊇ p` ("we just increase the weight of the edge
connecting this pair by adding the weights coming from all the hyperedges containing this pair").

**Formalization Note.** A pair of total weight `0` is still an edge, so `G_H` stays connected when
`H` is. -/
noncomputable def aeGraph (H : Hypergraph V) : Hypergraph V where
  edges := H.edges.biUnion (Finset.powersetCard 2)
  w := fun p => ∑ e ∈ H.edges with p ⊆ e, H.w e / ((e.card : ℝ) - 1)
  w_nonneg := by
    intro p hp
    obtain ⟨_, _, hp⟩ := Finset.mem_biUnion.mp hp
    have hcard : p.card = 2 := (Finset.mem_powersetCard.mp hp).2
    refine Finset.sum_nonneg fun e he => ?_
    obtain ⟨he, hpe⟩ := Finset.mem_filter.mp he
    have h2 : 2 ≤ e.card := hcard ▸ Finset.card_le_card hpe
    have h2' : (2 : ℝ) ≤ e.card := by exact_mod_cast h2
    exact div_nonneg (H.w_nonneg e he) (by linarith)
  card_ne_one := by
    intro p hp
    obtain ⟨_, _, hp⟩ := Finset.mem_biUnion.mp hp
    rw [(Finset.mem_powersetCard.mp hp).2]
    norm_num

end Hypergraph

end HyperCheeger


