-- Prove2me | Definitions.Def_BianchiIX_Analysis_CurveMeasurability
-- name    : BianchiIX_Analysis_CurveMeasurability
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T20:28:00.437201+00:00
-- url     : https://prove2.me/theorems/9c04d1ce-4584-488b-a249-e5d3a5a8d537
-- title:
--   Interior sampling steps for variable closed intervals
-- statement:
--   For real $l,r,x$ and $n\in\mathbb N$, define
--   $$h_n(l,r,x)=
--   \frac{\begin{cases}r-x,&x<r,\\l-x,&x\geq r\end{cases}}{3(n+1)}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CurveMeasurability.lean

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology



/-- The sign points into the interval, including at its right endpoint. -/
def curveSampleStep (l r x : ℝ) (n : ℕ) : ℝ :=
  (if x < r then r - x else l - x) / (3 * ((n : ℝ) + 1))















end BianchiIX


