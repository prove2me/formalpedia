-- Prove2me | Definitions.Def_SmoothedNash_Supplement_initDir
-- name    : SmoothedNash_Supplement_initDir
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:04:58.255859+00:00
-- url     : https://prove2.me/theorems/d079b1a1-9c53-4966-8f47-4521c11a6812
-- title:
--   Initial direction $v_{-1}$ of Algorithm 4
-- statement:
--   The initial direction of Algorithm 4 is the unit vector
--   $$
--   v_{-1} = \frac{(F(0)/a,\ 1)}{\sqrt{1 + \|F(0)\|^2/a^2}} \in \mathbb R^n \times \mathbb R, \qquad a = L_0 + L_1,
--   $$
--   which spans the kernel of $J_K(0,0) = [\,I \mid -F(0)/a\,]$ and points into $t > 0$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 4, line 6, p.28

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The initial direction `v_{−1} = (F(0)/a, 1)/√(1 + ‖F(0)‖²/a²)` of Algorithm 4 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53),
Algorithm 4, line 6, p.28), with `a = L0 + L1`, as a pair in `ℝ^n × ℝ`. -/
noncomputable def initDir {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (L0 L1 : ℝ) : EuclideanSpace ℝ (Fin n) × ℝ :=
  (Real.sqrt (1 + ‖F 0‖ ^ 2 / (L0 + L1) ^ 2))⁻¹ • ((L0 + L1)⁻¹ • F 0, (1 : ℝ))

end SmoothedNash.Supplement


