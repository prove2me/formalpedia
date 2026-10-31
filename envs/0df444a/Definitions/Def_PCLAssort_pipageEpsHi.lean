-- Prove2me | Definitions.Def_PCLAssort_pipageEpsHi
-- name    : PCLAssort_pipageEpsHi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:23.069145+00:00
-- url     : https://prove2.me/theorems/c9ac58b8-9800-4bc9-b8e4-06c14b05c359
-- title:
--   Right end of the pipage interval
-- statement:
--   The right end of the interval of steps in Definition 3 and in pipage rounding:
--
--   $$
--   \epsilon_{\mathrm{hi}}=\min\Big\{1-x_i,\ \tfrac{s_j}{s_i}x_j\Big\}.
--   $$
--
--   It is the largest step that keeps $x_i\le 1$ and $x_j\ge 0$.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Definition 3, p.794 (PDF p.10)

import Mathlib

namespace PCLAssort

/-- Right end `min{1 − x_i, (s_j/s_i) x_j}` of the ε-interval of Definition 3 (ε-convexity) and of
step 2 of pipage rounding (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.794). -/
noncomputable def pipageEpsHi {V : Type} (s : V → ℝ) (x : V → ℝ) (i j : V) : ℝ :=
  min (1 - x i) (s j / s i * x j)

end PCLAssort


