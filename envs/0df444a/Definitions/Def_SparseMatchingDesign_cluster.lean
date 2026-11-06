-- Prove2me | Definitions.Def_SparseMatchingDesign_cluster
-- name    : SparseMatchingDesign_cluster
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:37.375189+00:00
-- url     : https://prove2.me/theorems/02f39319-f7e0-4f5f-b275-af7f045ce100
-- title:
--   Cluster index $\lceil i/K\rceil$ of a node
-- statement:
--   In the $K$-cluster and $K$-ring designs the nodes $[n]$ are split into $n/K$ consecutive clusters of $K$ nodes; node $i$ lies in cluster $\lceil i/K\rceil\in\{1,\dots,n/K\}$.
--
--   **Formalization Note** With 0-based nodes $i\in\{0,\dots,n-1\}$ (paper node $i+1$) the 0-based cluster index is $\lfloor i/K\rfloor$, since $\lceil (i+1)/K\rceil=\lfloor i/K\rfloor+1$ for $K\ge1$.
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §5.3, p.18, eq. (6); §2.1, p.4

import Mathlib

namespace SparseMatchingDesign

/-- The (0-based) cluster index of a node in the `K`-cluster / `K`-ring designs: paper node
`i ∈ [n]` lies in cluster `⌈i/K⌉ ∈ {1, …, n/K}`.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §5.3, p.18, eq. (6) (the clusters ⌈i/K⌉); §2.1, p.4 (the partition V₁, …, V_m with
|V_ℓ| = K).

**Formalization Note** Node `i : Fin n` is paper node `i + 1`, and `⌈(i + 1)/K⌉ = i / K + 1`
for `K ≥ 1`, so the 0-based cluster index is `i / K ∈ {0, …, n/K − 1}` (natural-number
division). -/
def cluster (K : ℕ) {n : ℕ} (i : Fin n) : ℕ := i.val / K

end SparseMatchingDesign


