-- Prove2me | Definitions.Def_IntervalToDynamic_gammaParam
-- name    : IntervalToDynamic_gammaParam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:46.682484+00:00
-- url     : https://prove2.me/theorems/0cac602b-b3d0-45a6-b1d6-c5f4c24f9c2a
-- title:
--   Eq. (14): the wrapper parameter $\gamma$
-- statement:
--   For $D_{\mathcal X},G,\alpha>0$ and $D_{\mathcal Y}=2D_{\mathcal X}$, the wrapper sets
--   $$
--   \gamma=\frac12\min\Bigl\{\alpha,\ \frac1{D_{\mathcal X}G},\ \frac4{(D_{\mathcal X}+D_{\mathcal Y})G}\Bigr\}.
--   $$
--
--   This is the coefficient of the quadratic term of the exp-concave surrogate, Eq. (11).
--
--   **Formalization Note** $D_{\mathcal Y}$ is written out as $2D_{\mathcal X}$. The third term is inactive at $D_{\mathcal Y}=2D_{\mathcal X}$ and is kept as printed.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Eq. (14), p.9

import Mathlib

namespace IntervalToDynamic

/-- The wrapper's parameter `γ` of Eq. (14). Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Eq. (14), p.9:
`γ = ½ min{α, 1/(D_X G), 4/((D_X + D_Y) G)}`, with `D_Y = 2 D_X` from Eq. (13).

**Formalization Note.** `D_Y` is written out as `2 * DX`. The third term of the minimum is never
the smallest at `D_Y = 2 D_X`; it is kept as printed. -/
noncomputable def gammaParam (DX G α : ℝ) : ℝ :=
  (1 / 2) * min α (min (1 / (DX * G)) (4 / ((DX + 2 * DX) * G)))

end IntervalToDynamic


