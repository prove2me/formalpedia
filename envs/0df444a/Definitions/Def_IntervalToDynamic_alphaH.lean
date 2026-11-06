-- Prove2me | Definitions.Def_IntervalToDynamic_alphaH
-- name    : IntervalToDynamic_alphaH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:39.65604+00:00
-- url     : https://prove2.me/theorems/f1ab6866-fc41-4403-bdc7-4749e135b580
-- title:
--   Table 2: the exp-concavity coefficient $\alpha_h$
-- statement:
--   The exp-concavity coefficient of the surrogate on $\mathcal Y$ is
--   $$
--   \alpha_h=\frac{\gamma}{(1+\gamma D_{\mathcal Y}G)^2},
--   $$
--   with $D_{\mathcal Y}=2D_{\mathcal X}$ and $\gamma$ of Eq. (14).
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Table 2, p.9

import Mathlib
import Definitions.Def_IntervalToDynamic_gammaParam

namespace IntervalToDynamic

/-- The exp-concavity coefficient of the surrogate. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Table 2, p.9:
`α_h = γ / (1 + γ D_Y G)²`, with `D_Y = 2 D_X` and `γ` from Eq. (14). -/
noncomputable def alphaH (DX G α : ℝ) : ℝ :=
  gammaParam DX G α / (1 + gammaParam DX G α * (2 * DX) * G) ^ 2

end IntervalToDynamic


