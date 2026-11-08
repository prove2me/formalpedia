-- Prove2me | Definitions.Def_TightClock_credit
-- name    : TightClock_credit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:55:50.914011+00:00
-- url     : https://prove2.me/theorems/f634b7dc-6d20-4e6f-aadf-535044526298
-- title:
--   Credit $\ell_r(j)$, (6.10)
-- statement:
--   At depth $r$, the relevant value scale is $y_r=M^{-r}$. A bidder with cutoff $j$ has the credit
--
--   $$\ell_r(j):=\begin{cases}a\,y_j,& j\le r,\\ y_r\log C(\rho^{\,j-r}),& j>r,\end{cases}\qquad \ell_r(\bot):=0.$$
--
--   The two formulas agree at $j=r$, since $\log C(1)=a$.
--
--   **Formalization Note** The natural subtraction $j-r$ occurs only in the branch $j>r$, and the argument of the logarithm is at least $1$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.4, p.40 (PDF p.43), eq. (6.10)

import Mathlib
import Definitions.Def_TightClock_C
import Definitions.Def_TightClock_y
import Definitions.Def_TightClock_rho

set_option autoImplicit false

namespace TightClock

/-- The credit (6.10) of a bidder at depth `r`: `ℓ_r(j) = a y_j` for `j ≤ r`, `ℓ_r(j) = y_r log C(ρ^{j−r})`
for `j > r`, and `ℓ_r(⊥) = 0`. Afshinmehr et al., manuscript (STOC 2027 submission), §6.4, p.40 (PDF 43).

**Formalization Note** The natural subtraction `j - r` occurs only in the branch `j > r`. The argument of the
logarithm is at least `1`. The verification file proves that the branches agree at `j = r`. -/
noncomputable def credit (q L r : ℕ) : Option (Fin (L + 1)) → ℝ
  | none => 0
  | some j =>
    if j.val ≤ r then a q * y q L j.val
    else y q L r * Real.log (C q ((rho q L) ^ (j.val - r)))

end TightClock


