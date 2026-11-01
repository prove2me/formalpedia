-- Prove2me | Definitions.Def_MarkdownReadjust_NCond
-- name    : MarkdownReadjust_NCond
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:11:52.452656+00:00
-- url     : https://prove2.me/theorems/5f8166ed-351d-4a24-bd59-1e98bce2675c
-- title:
--   Condition on $N$ in Theorem 4
-- statement:
--   The number of price updates $N$ satisfies the condition of Theorem 4 for inventory $x_0$ if
--
--   $$
--   N\le\max\Big\{0,\ \Big\lfloor\frac{\ln(x_0+1)}{4\alpha\ln\ln(x_0+1)}-2\Big\rfloor\Big\}.
--   $$
--
--   It allows $N$ to grow like $\ln x_0/\ln\ln x_0$ and guarantees that the grid of update times is fine enough for the bounds of Appendix B.
--
--   **Formalization Note** The comparison is in the integers. When $\ln\ln(x_0+1)\le0$ the bound is $0$, so no $N\ge1$ satisfies it.
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), Theorem 4, p.20

import Mathlib

namespace MarkdownReadjust

/-- The condition on the number of price updates in Theorem 4 (Chen–Jasin, SSRN 3740871, p.20):
`N ≤ max{0, ⌊ln(x₀+1)/(4α ln ln(x₀+1)) − 2⌋}`, for initial inventory `x`.

**Formalization Note.** The floor is `Int.floor` of a real number and the comparison is in `ℤ`.
If `ln ln(x+1) ≤ 0` the quotient is `≤ 0` (or `0` by Lean's division by zero), so the bound is
`0` and no `N ≥ 1` satisfies it; such small `x` are exactly those the paper's condition excludes. -/
def NCond (α : ℝ) (N x : ℕ) : Prop :=
  (N : ℤ) ≤ max 0 ⌊Real.log ((x : ℝ) + 1) / (4 * α * Real.log (Real.log ((x : ℝ) + 1))) - 2⌋

end MarkdownReadjust


