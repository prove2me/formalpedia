-- Prove2me | Definitions.Def_LL_Decomp1535a_theta
-- name    : LL_Decomp1535a_theta
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-30T14:08:41.869103+00:00
-- url     : https://prove2.me/theorems/e63a2c83-124c-42f9-830e-2f34372a96eb
-- title:
--   Chebyshev theta function
-- statement:
--   $\theta(N)=\sum_{p\le N,\ p \text{ prime}} \log p$ as a real number, for natural $N$.

import Mathlib

namespace LL_Decomp1535a

noncomputable section

open MeasureTheory

noncomputable def theta (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p

end

end LL_Decomp1535a


