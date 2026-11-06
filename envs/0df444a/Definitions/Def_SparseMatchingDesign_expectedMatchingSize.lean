-- Prove2me | Definitions.Def_SparseMatchingDesign_expectedMatchingSize
-- name    : SparseMatchingDesign_expectedMatchingSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:16:31.539201+00:00
-- url     : https://prove2.me/theorems/c8064889-5cd2-41c1-8728-482dcedeab30
-- title:
--   Expected maximum matching size $\mathbb M(G)=\mathbb E[\mu(\widetilde G)]$
-- statement:
--   Let $G$ be a graph on $[n]$, and let $\widetilde G$ be the residual graph: the subgraph of $G$ induced by the random set $\widetilde V$ of surviving nodes. With $\mu(H)$ the cardinality of a maximum matching of $H$, the expected maximum matching size is
--   $$\mathbb M(G):=\mathbb E\big[\mu(\widetilde G)\big].$$
--   It is the performance measure of a graph design under random node deletion.
--
--   **Formalization Note** $\mu$ is the published matching number `TuranMatching.Clique.matchingNumber` (a supremum over matching subgraphs that is attained on a finite vertex type). The residual graph for the surviving set $S$ is the induced graph on the subtype of $S$.
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §2.1, p.4 (μ); §2.2, p.6, eq. (1)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_SparseMatchingDesign_expectation

namespace SparseMatchingDesign

/-- The expected maximum matching size `𝕄(G) := E[μ(G̃)]` of a graph `G` on `[n]` (eq. (1)),
where `G̃` is the residual graph induced by the random set `Ṽ` of surviving nodes and `μ` is
the matching number (the size of a maximum matching).

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §2.2, p.6, eq. (1): "For each subgraph G ∈ 𝔾, Ṽ induces a residual random subgraph G̃.
Denote by 𝕄(G) the expected cardinality of a maximum matching of G̃, i.e., 𝕄(G) := E[μ(G̃)]."
μ is defined on p.4: "We use μ(G) to denote the cardinality of a maximum matching in G."

**Formalization Note** μ is the published `TuranMatching.Clique.matchingNumber` (the supremum of
the edge counts of matching subgraphs, a maximum over a finite vertex type). The residual graph
for the surviving set `S` is the induced graph `G.induce S` on the vertex type `↥S`. -/
noncomputable def expectedMatchingSize {n : ℕ} (p : ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  expectation n p (fun S => (TuranMatching.Clique.matchingNumber (G.induce (S : Set (Fin n))) : ℝ))

end SparseMatchingDesign


