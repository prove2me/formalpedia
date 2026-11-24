-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:09.434901+00:00
-- url     : https://prove2.me/theorems/a708dbd8-9fb6-49a1-b927-ef14ace794f2
-- title:
--   Lintegral Ioi Of Real Mul
-- statement:
--   Definitions and structural lemmas for Lintegral Ioi Of Real Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LintegralIoiOfRealMul.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped ENNReal Pointwise
namespace ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
noncomputable def coneFun (G : ℝ → ℝ≥0∞) (z s : ℝ) : ℝ≥0∞ :=
  if 0 < z ^ 2 + s ∧ z ^ 2 + s < 1 then G (z / Real.sqrt (z ^ 2 + s)) else 0
noncomputable def coneConst : ℝ≥0∞ :=
  volume (Ioo (-π) π) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * (Iio (1 : ℝ)).indicator 1 r
end ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
namespace ReciprocityTheory.ChartRestriction.G.AI
open ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
end ReciprocityTheory.ChartRestriction.G.AI


