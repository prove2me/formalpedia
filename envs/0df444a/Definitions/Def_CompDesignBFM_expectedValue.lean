-- Prove2me | Definitions.Def_CompDesignBFM_expectedValue
-- name    : CompDesignBFM_expectedValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:57.670256+00:00
-- url     : https://prove2.me/theorems/6d164e00-813e-4f1a-9157-fcb7cf00cfd9
-- title:
--   Expected value of a randomized mechanism
-- statement:
--   The expected value of a randomized mechanism under the bids $c$ is $\mathbb E[v(S)]=\sum_j w_j\,v(S_j(c))$, where $S_j$ is the allocation of the $j$-th component. Taken at the true costs, it is the quantity compared to the benchmark.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Corollary A.1, p.40 (PDF 42)

import Mathlib
import Definitions.Def_CompDesignBFM_RandMechanism

namespace CompDesignBFM

/-- The expected value `E[v(S)]` of a randomized mechanism under truthful bidding `c`
(Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Corollary A.1, p.40, PDF 42): the weighted sum of the values of the components' allocations. -/
noncomputable def expectedValue {n : ℕ} (R : RandMechanism n) (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) : ℝ :=
  ∑ j, R.w j * v ((R.mech j).alloc c)

end CompDesignBFM


