-- Prove2me | Definitions.Def_SparseMatchingDesign_emptySubClusterCount
-- name    : SparseMatchingDesign_emptySubClusterCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:16:39.021564+00:00
-- url     : https://prove2.me/theorems/6143a1bd-00f5-4345-9ac0-f559c1b95315
-- title:
--   Number $X$ of empty residual sub-clusters
-- statement:
--   With $I_s=\mathbb 1\{|\widetilde C_s|=0\}$ the indicator that sub-cluster $s$ has no surviving node,
--   $$X:=\sum_{s=1}^{n/K} I_s$$
--   is the number of empty residual sub-clusters. Its expectation bounds the loss of the $K$-ring.
--
--   **Formalization Note** $X$ is a deterministic function of the surviving set $S$.
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §EC.4, p.ec6

import Mathlib
import Definitions.Def_SparseMatchingDesign_subCluster

namespace SparseMatchingDesign

/-- The number `X := Σ_{s=1}^{n/K} I_s` of empty residual sub-clusters, where
`I_s = 𝟙{|C̃_s| = 0}`.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §EC.4, p.ec6: "Let I_s = 𝟙{|C̃_s| = 0} be the indicator variable for the event that
sub-cluster s is empty. We also define X := Σ_{i=1}^{n/K} I_i to be the total number of empty
sub-clusters."

**Formalization Note** `X` is a deterministic function of the surviving set `S`; the
0-based sub-cluster indices are `0, …, n/K − 1`. -/
def emptySubClusterCount {n : ℕ} (K : ℕ) (S : Finset (Fin n)) : ℕ :=
  ((Finset.range (n / K)).filter (fun s => subCluster K S s = ∅)).card

end SparseMatchingDesign


