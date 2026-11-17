-- Prove2me | Definitions.Def_SampleRemoval_Supplement_dpWork
-- name    : SampleRemoval_Supplement_dpWork
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:17:55.579027+00:00
-- url     : https://prove2.me/theorems/c42489c2-b773-4d3b-9b11-bf56484efdf5
-- title:
--   Candidate-comparison count for the truncated min-plus dynamic program
-- statement:
--   For a truncation cap $K_{\max}$, the dynamic program examines $k=0,\ldots,\min(n_g,K)$ when filling the entry for group $g$ and total $K$. Its exact unit-cost comparison count is
--
--   $$\sum_g\sum_{K=0}^{K_{\max}}(\min\{n_g,K\}+1).$$
--
--   This cost model makes the $O(nK^*)$ statement in Theorem 4.1 an explicit instance-independent bound.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Section 4, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_SampleRemoval_Supplement_FixedEffectsModel

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- The exact number of candidate comparisons in one truncated min-plus DP table through cap
`Kmax`: for group `g` and total `K`, candidates are `k=0,…,min(n_g,K)` (Xu, Gao, Hu, STOC
2027 submission, Theorem 4.1 proof, p.7 (PDF p.9)). -/
def dpWork {Γ : ℕ} (M : FixedEffectsModel Γ) (Kmax : ℕ) : ℕ :=
  ∑ g, ∑ K ∈ Finset.range (Kmax + 1), (min (M.nobs g) K + 1)

end SampleRemoval.Supplement


