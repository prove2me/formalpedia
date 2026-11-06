-- Prove2me | Definitions.Def_SparseMatchingDesign_IsChainOfSubClusters
-- name    : SparseMatchingDesign_IsChainOfSubClusters
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:16:30.607197+00:00
-- url     : https://prove2.me/theorems/27a05f54-6da0-4ecb-8cfc-4b4bc65e80d9
-- title:
--   Chain of sub-clusters
-- statement:
--   A run of cyclically consecutive residual sub-clusters $\widetilde C_r,\dots,\widetilde C_{r+\ell-1}$ (indices modulo $n/K$) is a **chain of sub-clusters** if
--
--   1. every sub-cluster of the run is a clique of size at most $K$ in the residual $K$-ring, and
--   2. every node of a sub-cluster of the run is adjacent to every node of the next sub-cluster of the run.
--
--   This is the structure the paper shows every connected component of the residual $K$-ring has.
--
--   **Formalization Note** Adjacency is that of $R_{n,K}$, which for surviving nodes is the adjacency of the residual graph and of each of its induced subgraphs.
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §5.3, p.19; §EC.4, p.ec6

import Mathlib
import Definitions.Def_SparseMatchingDesign_kRing
import Definitions.Def_SparseMatchingDesign_subCluster

namespace SparseMatchingDesign

/-- The residual sub-clusters `C̃_r, C̃_{r+1}, …, C̃_{r+ℓ−1}` (indices modulo `n/K`) form a
**chain of sub-clusters** in the residual `K`-ring: every sub-cluster of the run is a clique of
size at most `K`, and every node of a sub-cluster is linked to every node of the next sub-cluster
of the run.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §5.3, p.19: "each component is a chain of sub-clusters, in the following sense: Every
sub-cluster in the component is a clique of size at most K, and every pair of nodes in adjacent
sub-clusters are linked"; §EC.4, p.ec6: "By a sub-cluster, we mean a clique of size at most K,
and all edges between nodes from adjacent sub-clusters in the same component are present".

**Formalization Note** Adjacency is that of `kRing n K`; for nodes of the surviving set it is the
adjacency of the residual graph `R̃_{n,K}` and of any induced subgraph of it containing them.
"Adjacent sub-clusters" of the run are consecutive ones, `(r + t)` and `(r + t + 1)` mod `n/K`. -/
def IsChainOfSubClusters {n : ℕ} (K : ℕ) (S : Finset (Fin n)) (r ℓ : ℕ) : Prop :=
  (∀ t < ℓ, (subCluster K S ((r + t) % (n / K))).card ≤ K ∧
      ∀ i ∈ subCluster K S ((r + t) % (n / K)), ∀ j ∈ subCluster K S ((r + t) % (n / K)),
        i ≠ j → (kRing n K).Adj i j) ∧
  (∀ t, t + 1 < ℓ → ∀ i ∈ subCluster K S ((r + t) % (n / K)),
      ∀ j ∈ subCluster K S ((r + t + 1) % (n / K)), (kRing n K).Adj i j)

end SparseMatchingDesign


