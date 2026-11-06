-- Prove2me | Definitions.Def_SparseMatchingDesign_kRing
-- name    : SparseMatchingDesign_kRing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:15:36.966421+00:00
-- url     : https://prove2.me/theorems/323133b4-7cc1-445d-9077-23748c1ffe5d
-- title:
--   The $K$-ring $R_{n,K}$
-- statement:
--   For $K\mid n$, the $K$-ring $R_{n,K}=([n],E^R_{n,K})$ links every pair of distinct nodes in the same cluster or in adjacent clusters, with the first and last clusters adjacent:
--   $$\{i,j\}\in E^R_{n,K}\iff \big|\lceil j/K\rceil-\lceil i/K\rceil\big|\le 1\ \text{ or }\ \{\lceil i/K\rceil,\lceil j/K\rceil\}=\{1,n/K\}.$$
--   It is the sparse design whose matching loss Theorem 3 bounds. For $n=8$, $K=2$ it has the 20 edges of Example 2.
--
--   **Formalization Note** Clusters are 0-based, so "$\lceil i/K\rceil=1$" is cluster $0$ and "$\lceil j/K\rceil=n/K$" is cluster $n/K-1$. Condition (2) of eq. (6) is applied to both orders of the unordered pair. The definition is total in $n,K$; the theorems assume $K\ge1$ and $K\mid n$.
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §5.3, p.18, eq. (6); §2.1, p.4 (K-Ring)

import Mathlib
import Definitions.Def_SparseMatchingDesign_cluster

namespace SparseMatchingDesign

/-- The `K`-ring `R_{n,K} = ([n], E^R_{n,K})`: `{i, j}` is an edge iff either the clusters of `i` and
`j` differ by at most one, or one of them is the first cluster and the other the last cluster
`n/K` (eq. (6)).

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §5.3, p.18, eq. (6): "{i,j} ∈ E^R_{n,K} if and only if: either (1) |⌈j/K⌉ − ⌈i/K⌉| ≤ 1;
or (2) ⌈i/K⌉ = 1 and ⌈j/K⌉ = n/K." Also §2.1, p.4 (K-Ring).

**Formalization Note** Clusters are 0-based (`cluster K i = i / K`), so "⌈i/K⌉ = 1" is
`cluster K i = 0` and "⌈j/K⌉ = n/K" is `cluster K j + 1 = n / K`. An edge is an unordered pair of
distinct nodes, so condition (2) is applied to both orders. The paper assumes `K ≥ 1` and
`K ∣ n` (footnote 5, p.19); the theorems carry these hypotheses. -/
def kRing (n K : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧
    (|(cluster K j : ℤ) - cluster K i| ≤ 1 ∨
      (cluster K i = 0 ∧ cluster K j + 1 = n / K) ∨
      (cluster K j = 0 ∧ cluster K i + 1 = n / K))
  symm := ⟨fun i j h => by
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h2 | h2 | h2
    · left; rwa [abs_sub_comm]
    · right; right; exact h2
    · right; left; exact h2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end SparseMatchingDesign


