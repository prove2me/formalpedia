-- Prove2me | Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
-- name    : Kyprianou_Ch03_TemperedStableMeasure
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:51:24.026088+00:00
-- url     : https://prove2.me/theorems/67860cde-3414-4fa0-b8b0-78a5d2c056a2
-- title:
--   Generalised tempered stable positive and signed Lévy measures
-- statement:
--   The one-sided tempered power-tail jump measures and their signed two-sided sum, with the negative component reflected from a positive measure.
-- source:
--   Kyprianou (2006), Exercise 3.4, printed p. 84; solution p. 314.

import Mathlib
open MeasureTheory
set_option autoImplicit false
namespace Kyprianou.Ch03
noncomputable def temperedStablePositiveMeasure
    (c alpha gamma : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity (fun x : ℝ =>
    ENNReal.ofReal (if 0 < x
      then c * Real.exp (-gamma * x) / (x ^ (1 + alpha)) else 0))
noncomputable def temperedStableSignedMeasure
    (cPlus alphaPlus gammaPlus cMinus alphaMinus gammaMinus : ℝ) :
    Measure ℝ :=
  temperedStablePositiveMeasure cPlus alphaPlus gammaPlus +
    Measure.map (fun x : ℝ => -x)
      (temperedStablePositiveMeasure cMinus alphaMinus gammaMinus)
end Kyprianou.Ch03


