-- Prove2me | Definitions.Def_CubeSampling_dimLowDeg
-- name    : CubeSampling_dimLowDeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:12.674017+00:00
-- url     : https://prove2.me/theorems/0a5ff053-1441-4f77-9dcd-8e628ab867b3
-- title:
--   $D_{d,k} = \dim P_{d,k} = \sum_{j \le \min(k,d)} \binom{d}{j}$
-- statement:
--   The dimension of $P_{d,k}$ is
--   $$
--   D_{d,k} = \sum_{j=0}^{\min(k,d)} \binom{d}{j}.
--   $$
--   It is the range of admissible model dimensions $m$ in the regression problem.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, p.3

import Mathlib

namespace CubeSampling

/-- `D_{d,k} = dim P_{d,k} = ∑_{j=0}^{min(k,d)} C(d, j)` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1, p.3). -/
def dimLowDeg (d k : ℕ) : ℕ := ∑ j ∈ Finset.range (min k d + 1), d.choose j

end CubeSampling


