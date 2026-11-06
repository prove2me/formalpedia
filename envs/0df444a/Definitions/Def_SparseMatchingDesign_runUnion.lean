-- Prove2me | Definitions.Def_SparseMatchingDesign_runUnion
-- name    : SparseMatchingDesign_runUnion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:16:23.840046+00:00
-- url     : https://prove2.me/theorems/1dd239f4-b8c4-46a3-831c-2b99f27e0948
-- title:
--   Union $\widetilde C_r\cup\dots\cup\widetilde C_s$ of a cyclic run of sub-clusters
-- statement:
--   For a start index $r$ and a length $\ell$, this is the union
--   $$\widetilde C_r\cup\widetilde C_{r+1}\cup\dots\cup\widetilde C_{r+\ell-1}$$
--   of $\ell$ cyclically consecutive residual sub-clusters, indices taken modulo $n/K$. It covers the increasing runs $r,\dots,s$ of Claim EC.1 and the wrapping runs $r,\dots,n/K,1,\dots,s$ of the remark after its proof.
--
--   **Formalization Note** The $t$-th sub-cluster of the run is $(r+t)\bmod (n/K)$ (0-based).
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §EC.4, Claim EC.1, p.ec6, and the remark on p.ec7

import Mathlib
import Definitions.Def_SparseMatchingDesign_subCluster

namespace SparseMatchingDesign

/-- The union `C̃_r ∪ C̃_{r+1} ∪ … ∪ C̃_{r+ℓ−1}` of `ℓ` cyclically consecutive residual
sub-clusters starting at `r`, indices taken modulo `n/K`.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §EC.4, Claim EC.1, p.ec6 ("the node set C̃_r ∪ C̃_{r+1} ∪ … ∪ C̃_s") and the remark after
its proof, p.ec7 ("If C̃_r, …, C̃_{n/K}, C̃_1, …, C̃_s are all non-empty, then Claim EC.1 also
applies to this sequence of node sets, because sub-clusters n/K and 1 are adjacent").

**Formalization Note** A run is given by its start `r` and length `ℓ`; the `t`-th sub-cluster of
the run is `(r + t) mod (n/K)` (0-based), which covers both the increasing runs r, …, s and the
wrapping runs r, …, n/K, 1, …, s of the paper. -/
def runUnion {n : ℕ} (K : ℕ) (S : Finset (Fin n)) (r ℓ : ℕ) : Finset (Fin n) :=
  (Finset.range ℓ).biUnion (fun t => subCluster K S ((r + t) % (n / K)))

end SparseMatchingDesign


