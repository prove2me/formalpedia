-- Prove2me | Definitions.Def_QKPSDP_mr
-- name    : QKPSDP_mr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:26.806247+00:00
-- url     : https://prove2.me/theorems/0819c12d-1006-459e-8a2b-621084ecd898
-- title:
--   The minimum rank $\operatorname{mr}(G)$ of a graph
-- statement:
--   For a simple undirected graph $G$ on $[n]$,
--
--   $$
--   \operatorname{mr}(G) := \min\{ \operatorname{rank}(A) : A \in \mathcal Q(G) \}. \qquad (19)
--   $$
--
--   A sparse pattern can force large rank; Lemma 4.10(ii) turns a large $\operatorname{mr}(G)$ into a weaker rank requirement on the factorization.
--
--   **Formalization Note** Written as an infimum over $\mathbb N$; the set is nonempty (it contains the rank of the adjacency matrix), so it is the minimum.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, (19), p.10

import Mathlib
import Definitions.Def_QKPSDP_QG

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, (19), p.10: the minimum rank of `G`,
`mr(G) := min { rank(A) : A ∈ Q(G) }`.

**Formalization Note** Written as `sInf` over `ℕ`. The set is never empty (the adjacency matrix
of `G` lies in `Q(G)`), so the infimum is attained and equals the paper's minimum; it is never
the junk value `sInf ∅ = 0`. -/
noncomputable def mr {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k | ∃ A ∈ QG G, A.rank = k}

end QKPSDP


