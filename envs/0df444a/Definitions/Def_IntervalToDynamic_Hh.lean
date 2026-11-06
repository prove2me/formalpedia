-- Prove2me | Definitions.Def_IntervalToDynamic_Hh
-- name    : IntervalToDynamic_Hh
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:37.450323+00:00
-- url     : https://prove2.me/theorems/527f04b0-2755-4228-8589-08cf419e2aa0
-- title:
--   Table 2: the smoothness coefficient $H_h$
-- statement:
--   The smoothness coefficient of the surrogate is
--   $$
--   H_h=\frac{2G_h}{D_{\mathcal X}}.
--   $$
--
--   It is used only in the hindsight analysis, not by the algorithm.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Table 2, p.9

import Mathlib
import Definitions.Def_IntervalToDynamic_Gh

namespace IntervalToDynamic

/-- The smoothness coefficient of the surrogate. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Table 2, p.9: `H_h = 2 G_h / D_X`, used
"only in hindsight analysis". -/
noncomputable def Hh (mode : LossMode) (DX G : ℝ) : ℝ :=
  2 * Gh mode DX G / DX

end IntervalToDynamic


