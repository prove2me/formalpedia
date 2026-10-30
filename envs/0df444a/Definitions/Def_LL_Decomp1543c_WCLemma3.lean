-- Prove2me | Definitions.Def_LL_Decomp1543c_WCLemma3
-- name    : LL_Decomp1543c_WCLemma3
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T17:30:44.533464+00:00
-- url     : https://prove2.me/theorems/f5bac173-46ae-45c4-a831-ede6a2cb9830
-- title:
--   Statement of the Wang and Chen kernel sum bound
-- statement:
--   The proposition that for all real $\alpha$, integer $a$, natural $q$ with $\operatorname{Dioph}(\alpha,a,q)$ and $q\ge15$, and all real $X\ge1$, $Y>0$: $\sum_{n=1}^{\lfloor X\rfloor}K(Y/n,\alpha n)\le5q+1.5\,q\log q+X\log q+5(Y/q)\log X$.

import Mathlib
import Definitions.Def_LL_Decomp1543c_minK
import Definitions.Def_LL_Decomp1543c_Dioph

namespace LL_Decomp1543c

open Real Finset ArithmeticFunction

def WCLemma3 : Prop :=
  ∀ (α : ℝ) (a : ℤ) (q : ℕ), Dioph α a q → 15 ≤ q → ∀ X Y : ℝ, 1 ≤ X → 0 < Y →
    ∑ n ∈ Icc 1 ⌊X⌋₊, minK (Y / n) (α * n) ≤
      5 * q + 1.5 * q * Real.log q + X * Real.log q + 5 * Y / q * Real.log X

end LL_Decomp1543c


