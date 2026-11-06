-- Prove2me | Definitions.Def_SparseMatchingDesign_matchingLoss
-- name    : SparseMatchingDesign_matchingLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:17:38.991321+00:00
-- url     : https://prove2.me/theorems/617acb28-3a1e-4f8b-a313-9306ce682bff
-- title:
--   Matching loss $L(G)=2[\mathbb M(G^{\mathrm{in}})-\mathbb M(G)]$
-- statement:
--   For a subgraph $G$ of the input graph $G^{\rm in}$ on the same node set,
--   $$L(G):=2\big[\mathbb M(G^{\rm in})-\mathbb M(G)\big],$$
--   the expected number of additional unmatched surviving nodes in $\widetilde G$ compared with $\widetilde{G^{\rm in}}$. Theorem 3 bounds it for the $K$-ring when $G^{\rm in}=K_n$.
--
--   **Formalization Note** The input graph is an explicit argument; the complete graph $K_n$ is `⊤`.
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §2.2, p.6, eq. (2)

import Mathlib
import Definitions.Def_SparseMatchingDesign_expectedMatchingSize

namespace SparseMatchingDesign

/-- The matching loss `L(G) := 2 [𝕄(G^in) − 𝕄(G)]` of a subgraph `G` of the input graph
`G^in` (eq. (2)): the expected number of additional unmatched surviving nodes in `G̃` compared
with `G̃^in`.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §2.2, p.6, eq. (2): "L(G) := 2 [𝕄(G^in) − 𝕄(G)]".

**Formalization Note** The input graph `Gin` is an explicit argument; §5 (and Theorem 3) takes
`Gin = Kₙ`, which is `⊤ : SimpleGraph (Fin n)`. -/
noncomputable def matchingLoss {n : ℕ} (p : ℝ) (Gin G : SimpleGraph (Fin n)) : ℝ :=
  2 * (expectedMatchingSize p Gin - expectedMatchingSize p G)

end SparseMatchingDesign


