-- Prove2me | Definitions.Def_SparseMatchingDesign_subCluster
-- name    : SparseMatchingDesign_subCluster
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:15:35.617862+00:00
-- url     : https://prove2.me/theorems/cbaeb8de-de28-4618-89c8-60438389f39b
-- title:
--   Residual sub-cluster $\widetilde C_s$
-- statement:
--   Given the set $S$ of surviving nodes, the $s$-th residual sub-cluster $\widetilde C_s$ is the set of surviving nodes of cluster $s$, $s\in[n/K]$. It has at most $K$ nodes and may be empty.
--
--   **Formalization Note** Sub-cluster indices are 0-based: paper index $s$ is $s-1$.
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §EC.4, p.ec6

import Mathlib
import Definitions.Def_SparseMatchingDesign_cluster

namespace SparseMatchingDesign

/-- The `s`-th residual sub-cluster `C̃_s`: the surviving nodes (those in `S`) of cluster `s`.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §EC.4, p.ec6: "The n/K clusters in R_{n,K} give rise to n/K residual sub-clusters of size at
most K in R̃_{n,K}, and we use C̃_s to denote the set of nodes in the s-th residual sub-cluster,
s ∈ [n/K]."

**Formalization Note** Clusters are 0-based: paper sub-cluster `s ∈ [n/K]` is index `s − 1`. -/
def subCluster {n : ℕ} (K : ℕ) (S : Finset (Fin n)) (s : ℕ) : Finset (Fin n) :=
  S.filter (fun i => cluster K i = s)

end SparseMatchingDesign


