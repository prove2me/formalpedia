-- Prove2me | Definitions.Def_EffHorizonProphet_yFun
-- name    : EffHorizonProphet_yFun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:42:28.915209+00:00
-- url     : https://prove2.me/theorems/b76d3b52-72c3-4bb2-9a81-4197dd891c09
-- title:
--   The function $y(x)$
-- statement:
--   For $x>0$,
--   $$y(x)=\frac{A_S(x)}{x^2A_S'(x)}-\frac1x.$$
--   The sign of $\partial_xf_S(x,y)$ equals the sign of $y-y(x)$, which is why this function selects the worst common value.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Eq. (21), p.22

import Mathlib
import Definitions.Def_EffHorizonProphet_AS

namespace EffHorizonProphet

/-- The function `y(x) = A_S(x) / (x² A_S'(x)) - 1/x` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Eq. (21), p.22), for `x > 0`. `A_S` is
smooth, so `deriv` is its derivative (see the sanity file). -/
noncomputable def yFun (S : ℕ) (γ x : ℝ) : ℝ :=
  AS S γ x / (x ^ 2 * deriv (AS S γ) x) - 1 / x

end EffHorizonProphet


