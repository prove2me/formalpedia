-- Prove2me | Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
-- name    : Submission_Weighted_Parameters_w3sum_e1ae71d
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T07:21:18.664846+00:00
-- url     : https://prove2.me/theorems/1facd3a8-eea0-4bf6-bb99-61399c4129d5
-- title:
--   Sharper weighted-cache 3SUM: exact numerical parameters
-- statement:
--   Exact rational parameters of the refined weighted-cache 3SUM analysis. This version keeps its constants separate from the previous published solver.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
set_option autoImplicit false
noncomputable section
namespace WeightedCacheParameters_e1ae71d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
def pi0 : ℝ := (406027953884819 / 500000000000000 : ℝ)
def pi1 : ℝ := (39662773613067 / 250000000000000 : ℝ)
def pi2 : ℝ := (14646498889047 / 500000000000000 : ℝ)
def alpha0 : ℝ := (90114578758847 / 100000000000000 : ℝ)
def alpha1 : ℝ := (5568117488677 / 62500000000000 : ℝ)
def alpha2 : ℝ := (4882166296349 / 500000000000000 : ℝ)
def deficit : ℝ := (134483535964511 / 10000000000000000 : ℝ)
def yRoot : ℝ := (199750991630287 / 200000000000000 : ℝ)
def zRoot : ℝ := (49905618228487 / 50000000000000 : ℝ)
def cutSlope : ℝ := (2790453661435908961 / 10000000000000000 : ℝ)
def dropSlope : ℝ := (184107960735415559 / 10000000000000000 : ℝ)
def targetExponent : ℝ := (2400349260231 / 1250000000000 : ℝ)
def bankArg : ℝ := 1 + yRoot ^ 1369 + yRoot ^ 2740
def queryArg1 : ℝ := 1 + zRoot ^ 1369
def queryArg2 : ℝ := 1 + zRoot ^ 1371 + zRoot ^ 2740
def Hn : ℝ := -pi0 * Real.log pi0 - pi1 * Real.log pi1 - pi2 * Real.log pi2
def An : ℝ := -alpha0 * Real.log alpha0 - alpha1 * Real.log alpha1 - alpha2 * Real.log alpha2
def Gn : ℝ := pi1 * Real.log 2 + pi2 * Real.log 3
def Bn : ℝ := Real.log bankArg - cutSlope * Real.log yRoot
def Qn : ℝ := pi1 * Real.log queryArg1 + pi2 * Real.log queryArg2 - dropSlope * Real.log zRoot
def proposedLedger : List ℝ :=
  [2 * Bn / Hn, (2 * Hn - Gn + 2 * Qn) / Hn,
   2 * An / Hn, (Hn + Gn) / Hn, (2 * Hn - Gn) / Hn, 1]
end WeightedCacheParameters_e1ae71d


