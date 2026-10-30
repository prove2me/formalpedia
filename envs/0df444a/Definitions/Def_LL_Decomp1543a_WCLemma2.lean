-- Prove2me | Definitions.Def_LL_Decomp1543a_WCLemma2
-- name    : LL_Decomp1543a_WCLemma2
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:36:52.692168+00:00
-- url     : https://prove2.me/theorems/e903433f-5563-444b-be9c-57c873026ecd
-- title:
--   Wang and Chen short-interval kernel estimate
-- statement:
--   Define $\mathrm{WCLemma2}$ to assert that, for all $\operatorname{Dioph}(\alpha,a,q)$, real $X>0$, natural $Y\ge1$ and integer $Z$, $\sum_{Z<n\le Z+Y}K(X,\alpha n)\le(\lfloor Y/q\rfloor+1)(5X+q\log q)$, where $n$ ranges over integers and $Y/q$ is natural-number division.

import Mathlib
import Definitions.Def_LL_Decomp1543a_nint
import Definitions.Def_LL_Decomp1543a_minK
import Definitions.Def_LL_Decomp1543a_Dioph

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
def WCLemma2 : Prop :=
  ∀ (α : ℝ) (a : ℤ) (q : ℕ), Dioph α a q → ∀ X : ℝ, 0 < X → ∀ (Y : ℕ) (Z : ℤ), 1 ≤ Y →
    ∑ n ∈ Ioc Z (Z + Y), minK X (α * n) ≤ (((Y / q : ℕ) : ℝ) + 1) * (5 * X + q * Real.log q)
end LL_Decomp1543a


