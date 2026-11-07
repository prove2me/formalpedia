-- Prove2me | Definitions.Def_EffHorizonProphet_yStar
-- name    : EffHorizonProphet_yStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:50.923782+00:00
-- url     : https://prove2.me/theorems/c4725730-9b66-4a4b-a2c4-b591862e139c
-- title:
--   The common value $y_{\tilde\gamma}$
-- statement:
--   The common value of the hard instance is $y_{\tilde\gamma}=y(x_{\tilde\gamma})$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Eq. (22), p.22

import Mathlib
import Definitions.Def_EffHorizonProphet_yFun
import Definitions.Def_EffHorizonProphet_xStar

namespace EffHorizonProphet

/-- The value `y_γ̃ = y(x_γ̃)` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Eq. (22), p.22), the common value of the hard instance. -/
noncomputable def yStar (S : ℕ) (γ : ℝ) : ℝ :=
  yFun S γ (xStar S γ)

end EffHorizonProphet


