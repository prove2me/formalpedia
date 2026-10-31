-- Prove2me | Definitions.Def_PCLAssort_pipageEpsLo
-- name    : PCLAssort_pipageEpsLo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:16.978669+00:00
-- url     : https://prove2.me/theorems/1b1f24fc-9d2f-497a-a308-f5e0a034668c
-- title:
--   Left end of the pipage interval
-- statement:
--   The left end of the interval of steps in Definition 3 and in pipage rounding:
--
--   $$
--   \epsilon_{\mathrm{lo}}=-\min\Big\{x_i,\ \tfrac{s_j}{s_i}(1-x_j)\Big\}.
--   $$
--
--   It is the most negative step that keeps $x_i\ge 0$ and $x_j\le 1$.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Definition 3, p.794 (PDF p.10)

import Mathlib

namespace PCLAssort

/-- Left end `−min{x_i, (s_j/s_i)(1 − x_j)}` of the ε-interval of Definition 3 (ε-convexity) and of
step 2 of pipage rounding (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.794). -/
noncomputable def pipageEpsLo {V : Type} (s : V → ℝ) (x : V → ℝ) (i j : V) : ℝ :=
  -min (x i) (s j / s i * (1 - x j))

end PCLAssort


