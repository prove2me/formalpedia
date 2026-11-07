-- Prove2me | Definitions.Def_EffHorizonProphet_xStar
-- name    : EffHorizonProphet_xStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:59.755631+00:00
-- url     : https://prove2.me/theorems/08ad6438-3890-4a93-87bd-4b5607a05cf7
-- title:
--   The special point $x_{\tilde\gamma}$
-- statement:
--   The **special point** is $x_{\tilde\gamma}=1/c_{\tilde\gamma}$. It equals $\frac{S(1-\tilde\gamma)}{1-\tilde\gamma^S}$ for $\tilde\gamma<1$ and $1$ for $\tilde\gamma=1$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Eq. (20), p.22

import Mathlib
import Definitions.Def_EffHorizonProphet_cGamma

namespace EffHorizonProphet

/-- The special point `x_γ̃ = 1 / c_γ̃` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Eq. (20), p.22). -/
noncomputable def xStar (S : ℕ) (γ : ℝ) : ℝ :=
  1 / cGamma S γ

end EffHorizonProphet


