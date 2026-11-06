-- Prove2me | Definitions.Def_IntervalToDynamic_Gh
-- name    : IntervalToDynamic_Gh
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:30.302119+00:00
-- url     : https://prove2.me/theorems/5ab4823f-2a35-4577-8c2d-14ed340a2dc5
-- title:
--   Table 2: the Lipschitz coefficient $G_h$
-- statement:
--   The Lipschitz coefficient of the surrogate on $\mathcal Y$, with $D_{\mathcal Y}=2D_{\mathcal X}$ and $\gamma$ of Eq. (14), is
--   $$
--   G_h=\begin{cases}G&\text{convex},\\(1+\gamma D_{\mathcal Y}G)\,G&\text{exp-concave},\\G+\dfrac{\lambda(D_{\mathcal X}+D_{\mathcal Y})}2&\text{strongly convex.}\end{cases}
--   $$
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Table 2, p.9

import Mathlib
import Definitions.Def_IntervalToDynamic_LossMode
import Definitions.Def_IntervalToDynamic_gammaParam

namespace IntervalToDynamic

/-- The Lipschitz coefficient `G_h` of the surrogate on `Y`. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Table 2, p.9:
`G_h = G` (convex), `G_h = (1 + γ D_Y G) G` (exp-concave), `G_h = G + λ (D_X + D_Y)/2` (strongly
convex), with `D_Y = 2 D_X` and `γ` from Eq. (14). -/
noncomputable def Gh (mode : LossMode) (DX G : ℝ) : ℝ :=
  match mode with
  | .convex => G
  | .expConcave α => (1 + gammaParam DX G α * (2 * DX) * G) * G
  | .stronglyConvex lam => G + lam * (DX + 2 * DX) / 2

end IntervalToDynamic


