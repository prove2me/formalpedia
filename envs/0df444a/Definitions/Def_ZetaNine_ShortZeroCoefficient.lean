-- Prove2me | Definitions.Def_ZetaNine_ShortZeroCoefficient
-- name    : ZetaNine_ShortZeroCoefficient
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-02T15:07:55.730756+00:00
-- url     : https://prove2.me/theorems/50eafaec-696e-4a0f-809d-bd988c671e52
-- title:
--   The actual finite short-zero coefficient
-- statement:
--   Define the exact natural binomial weight $w_{n,m,r,b}(j)=\binom{n}{j}^{r}[\binom{j+m}{m}\binom{n-j+m}{m}]^{b}$ and the genuine integer short-zero coefficient $A_{n,m}=28\sum_{j=0}^{n}(-1)^{m+j}w_{n,m,3,7}(j)$. These are definitions only; no sign, nonvanishing, gamma identity or analytic assumption is embedded.
-- source:
--   https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02; research/short-zero-coefficient-nonvanishing.md, section 1 (the exact A_(n,m) definition and equation (1)), section 6 (equation (3) and the terminating Dixon factorial formula), section 7 (the coefficient nonvanishing conclusion).

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Basic

set_option autoImplicit false
open scoped BigOperators

namespace ZetaNine.ShortZeroCoefficient

/-- The exact integer coefficient of `z^j` in the weighted Franel polynomial. -/
def weightedCoeff (n m r b j : ℕ) : ℕ :=
  n.choose j ^ r * ((j + m).choose m * (n - j + m).choose m) ^ b

/-- The genuine finite sum from the C3 note, rather than an abstract positive sum. -/
def A (n m : ℕ) : ℤ :=
  28 * ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ (m + j) *
    (weightedCoeff n m 3 7 j : ℤ)

end ZetaNine.ShortZeroCoefficient


