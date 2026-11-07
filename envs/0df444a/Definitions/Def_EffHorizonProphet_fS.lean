-- Prove2me | Definitions.Def_EffHorizonProphet_fS
-- name    : EffHorizonProphet_fS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:42:30.924048+00:00
-- url     : https://prove2.me/theorems/97f36273-9196-49a5-893b-284077ad6e63
-- title:
--   The limit ratio $f_S$
-- statement:
--   For $x>0$ and $y\ge0$,
--   $$f_S(x,y)=\frac{\big(\frac1x+y\big)A_S(x)}{y+c_{\tilde\gamma}}.$$
--   It is the limit of the ratio of the gambler's bound to the prophet value on the hard instance with common value $y$, when $np\to x$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Eq. (17), p.22

import Mathlib
import Definitions.Def_EffHorizonProphet_AS
import Definitions.Def_EffHorizonProphet_cGamma

namespace EffHorizonProphet

/-- The limit ratio `f_S(x, y) = (1/x + y) A_S(x) / (y + c_γ̃)` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Eq. (17), p.22), for `x > 0`,
`y ≥ 0`. -/
noncomputable def fS (S : ℕ) (γ x y : ℝ) : ℝ :=
  (1 / x + y) * AS S γ x / (y + cGamma S γ)

end EffHorizonProphet


