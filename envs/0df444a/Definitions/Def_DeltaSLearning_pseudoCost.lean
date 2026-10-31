-- Prove2me | Definitions.Def_DeltaSLearning_pseudoCost
-- name    : DeltaSLearning_pseudoCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:33.974463+00:00
-- url     : https://prove2.me/theorems/1e7bbc96-a988-404f-9335-e9dd5898fb06
-- title:
--   Pseudo cost $\tilde C$ of one period (7)
-- statement:
--   For one period with beginning inventory $x$, after-order level $y$ (order $q=y-x$) and demand $d$, the pseudo cost is
--   $$\tilde C(x,y,d) := K\,\mathbf 1(y>x)+c\,(y-x)+h\,(y-d)^+-p\min(y,d).$$
--   It equals the period cost (1), $K\mathbf 1(q>0)+cq+h(y-d)^++p(y-d)^-$, minus $p\,d$. The subtracted term does not depend on the policy, and unlike the lost-sales term the pseudo cost is observable from sales.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (7), p.11; eq. (1), p.8

import Mathlib
import Definitions.Def_DeltaSLearning_Params

namespace DeltaSLearning

/-- The pseudo cost (7) of one period with beginning inventory `x`, after-order level `y`
(so the order is `q = y - x`) and demand `d`:
`C̃ = K·1(q > 0) + c q + h (y - d)⁺ - p min(y, d)`. It is the period cost (1) minus `p d`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (7), p.11, and eq. (1), p.8. -/
noncomputable def pseudoCost (cp : Params) (x y d : ℝ) : ℝ :=
  cp.K * (if x < y then 1 else 0) + cp.c * (y - x) + cp.h * max (y - d) 0 - cp.p * min y d

end DeltaSLearning


