-- Prove2me | Definitions.Def_LL_Decomp1535a_S
-- name    : LL_Decomp1535a_S
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-30T14:08:03.907622+00:00
-- url     : https://prove2.me/theorems/8b6ec3c6-140a-44d8-aa78-2166d003ccb6
-- title:
--   Prime exponential sum
-- statement:
--   For a natural number $N$ and real $\alpha$, $S_N(\alpha)=\sum_{p\le N,\ p \text{ prime}} \log p \cdot e^{2\pi i \alpha p}$, a complex number.

import Mathlib

namespace LL_Decomp1535a

noncomputable section

open MeasureTheory

noncomputable def S (N : ℕ) (α : ℝ) : ℂ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
    (Real.log p : ℂ) * Complex.exp (2 * Real.pi * Complex.I * α * p)

end

end LL_Decomp1535a


