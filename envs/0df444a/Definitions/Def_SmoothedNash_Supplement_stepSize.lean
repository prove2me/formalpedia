-- Prove2me | Definitions.Def_SmoothedNash_Supplement_stepSize
-- name    : SmoothedNash_Supplement_stepSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:04:45.549211+00:00
-- url     : https://prove2.me/theorems/6eda146e-782c-4088-a877-70598dd8f6eb
-- title:
--   Step size $h = \min\{\theta/(64L_J), \varepsilon/(128a)\}$ of Algorithm 4
-- statement:
--   The predictor step size of Algorithm 4 is
--   $$
--   h = \min\Bigl\{ \frac{\theta}{64 L_J},\; \frac{\varepsilon}{128 a} \Bigr\}, \qquad a = L_0 + L_1 .
--   $$
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), p.28 and Algorithm 4, line 5

import Mathlib
import Definitions.Def_SmoothedNash_Supplement_lipJK
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The step size `h = min{θ/(64 L_J), ε/(128 a)}` of Algorithm 4 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.28 and
Algorithm 4, line 5), with `a = L0 + L1` and `L_J = lipJK L0 L1 L2`. -/
noncomputable def stepSize (L0 L1 L2 ε θ : ℝ) : ℝ :=
  min (θ / (64 * lipJK L0 L1 L2)) (ε / (128 * (L0 + L1)))

end SmoothedNash.Supplement


