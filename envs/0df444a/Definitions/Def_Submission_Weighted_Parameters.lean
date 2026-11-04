-- Prove2me | Definitions.Def_Submission_Weighted_Parameters
-- name    : Submission_Weighted_Parameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:50:40.432324+00:00
-- url     : https://prove2.me/theorems/5e371f23-eb3e-4054-9026-45badf3224c4
-- title:
--   Parameters
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Parameters.lean

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
set_option autoImplicit false
noncomputable section
namespace WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
def pi0 : ℝ := (8120584037 / 10000000000 : ℝ)
def pi1 : ℝ := (198333677 / 1250000000 : ℝ)
def pi2 : ℝ := (292746547 / 10000000000 : ℝ)
def alpha0 : ℝ := (13517251391 / 15000000000 : ℝ)
def alpha1 : ℝ := (2672750671 / 30000000000 : ℝ)
def alpha2 : ℝ := (292746547 / 30000000000 : ℝ)
def deficit : ℝ := (134483020951 / 10000000000000 : ℝ)
def yRoot : ℝ := (199334926009 / 200000000000 : ℝ)
def zRoot : ℝ := (497480529693 / 500000000000 : ℝ)
def cutSlope : ℝ := (130448080617511 / 1250000000000 : ℝ)
def dropSlope : ℝ := (134483020951 / 19531250000 : ℝ)
def targetExponent : ℝ := (96013971 / 50000000 : ℝ)
def bankArg : ℝ := 1 + yRoot ^ 512 + yRoot ^ 1025
def queryArg1 : ℝ := 1 + zRoot ^ 512
def queryArg2 : ℝ := 1 + zRoot ^ 513 + zRoot ^ 1025
def Hn : ℝ := -pi0 * Real.log pi0 - pi1 * Real.log pi1 - pi2 * Real.log pi2
def An : ℝ := -alpha0 * Real.log alpha0 - alpha1 * Real.log alpha1 - alpha2 * Real.log alpha2
def Gn : ℝ := pi1 * Real.log 2 + pi2 * Real.log 3
def Bn : ℝ := Real.log bankArg - cutSlope * Real.log yRoot
def Qn : ℝ := pi1 * Real.log queryArg1 + pi2 * Real.log queryArg2 - dropSlope * Real.log zRoot
def proposedLedger : List ℝ :=
  [2 * Bn / Hn, (2 * Hn - Gn + 2 * Qn) / Hn,
   2 * An / Hn, (Hn + Gn) / Hn, (2 * Hn - Gn) / Hn, 1]
end WeightedCacheParameters


