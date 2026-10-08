-- Prove2me | Definitions.Def_ZetaNine_AnalyticPhase
-- name    : ZetaNine_AnalyticPhase
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-07T12:11:40.014011+00:00
-- url     : https://prove2.me/theorems/94cac88d-1457-4674-8883-c589270a25a8
-- title:
--   Actual phase and auxiliary functions for zeta(9)
-- statement:
--   Define f(x)=10x log(x)+(x+2)log(x+2)-(x-1)log(x-1)-10(x+1)log(x+1), its derivative ratio, and the auxiliary functions used for its whole-domain upper bound.
-- source:
--   ZetaNine local research, AnalyticPhase.lean and AnalyticPhaseUpperBound.lean; independently compiled exports SHA-256 2b53b56f103bc69322c35d18e120c248cc34402fe831b7be86651f584d3bf4bd and 388c2be7c6401e0b0944e5ee9601ddd4f9359f85d05319ce191e6c6a4d0f1635. Native independent audit SHA-256 f487b27f1668432926ad505e4f30a67e41c1abf75ad9690cc2c84369487067cc.

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace ZetaNine.AnalyticPhase

def phase (x : ℝ) : ℝ :=
  10 * x * Real.log x + (x + 2) * Real.log (x + 2) -
    (x - 1) * Real.log (x - 1) - 10 * (x + 1) * Real.log (x + 1)

def phaseRatio (x : ℝ) : ℝ := (x + 2) * x ^ 10 / ((x - 1) * (x + 1) ^ 10)

def phaseSlope (x : ℝ) : ℝ :=
  10 * Real.log x + Real.log (x + 2) - Real.log (x - 1) - 10 * Real.log (x + 1)

def upperSlopeConstant : ℝ := (301 / 100 : ℝ) * (101 / 201 : ℝ) ^ 10

def smoothPhaseGap (x : ℝ) : ℝ :=
  10 * x * Real.log x + (x + 2) * Real.log (x + 2) -
    10 * (x + 1) * Real.log (x + 1) - phase 1 -
      (x - 1) * (1 + Real.log upperSlopeConstant)

def smoothPhaseSlope (x : ℝ) : ℝ :=
  10 * Real.log x + Real.log (x + 2) - 10 * Real.log (x + 1) -
    Real.log upperSlopeConstant

def smoothPhaseRatio (x : ℝ) : ℝ :=
  (x + 2) * (x / (x + 1)) ^ 10

end ZetaNine.AnalyticPhase


