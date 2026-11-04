-- Prove2me | Definitions.Def_Submission_ThreeSum_Parameters
-- name    : Submission_ThreeSum_Parameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:45:44.482167+00:00
-- url     : https://prove2.me/theorems/be4fc6a7-1ccd-4dbb-adc1-b5ef1ea358f9
-- title:
--   Parameters
-- statement:
--   Definitions and structural lemmas for Parameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option autoImplicit false
noncomputable section
namespace ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
noncomputable def entropy (t : ℝ) : ℝ := Real.binEntropy t / Real.log 2
noncomputable def E : ℝ := 128 * entropy (1 / 256)
noncomputable def kappa : ℝ :=
  512 * entropy (1 / 512) - 256 * entropy (1 / 256) - 1
noncomputable def gamma (t : ℝ) : ℝ :=
  256 * entropy (1 / 256) - 256 * entropy ((1 - t) / 256)
def phi (t : ℝ) : ℝ := 799 / 100 * t + 18 / 25 * t ^ 2 + 6 / 25 * t ^ 3
def phiDeriv (t : ℝ) : ℝ := 799 / 100 + 36 / 25 * t + 18 / 25 * t ^ 2
def epsilon : ℝ := 1 / 5
def bandShift : ℝ := -(1 / 20)
def boxSaving : ℝ := 191 / 1000
def terminalFraction : ℝ := 13 / 20
def entropyRatio : ℝ := 277 / 1000
def initialTheta : ℝ := 1 / 25
def tangentPoint : ℝ := 17 / 100
def kappaCap : ℝ := 3 / 2000
def certificateExponent : ℝ := 9809107 / 5000000
def targetExponent : ℝ := 981 / 500
noncomputable def tangentA : ℝ := (Real.log 100 - Real.log 83) / Real.log 2
noncomputable def tangentB : ℝ := (Real.log 83 - Real.log 17) / Real.log 2
noncomputable def gammaNumerator (t : ℝ) : ℝ :=
  (1 - t) * Real.log (1 - t) + (255 + t) * Real.log (255 + t) - 255 * Real.log 255
def switchThreshold (a : ℝ) : ℝ := (boxSaving - 2 * bandShift + a) / (1 - a)
def costLedger (e k h : ℝ) : List ℝ :=
  [2 * epsilon * e,
   1 + epsilon * (e - bandShift),
   2 - epsilon * boxSaving,
   2 - epsilon * (1 / 2 + bandShift - h),
   2 - epsilon * (1 / 2 - bandShift - k - entropyRatio * (1 + boxSaving - 2 * bandShift)),
   2 - epsilon * (terminalFraction - 1 / 2 - bandShift - k),
   epsilon * (8 / 5) * (e + 1 / 2),
   2 + epsilon * (4 / 5 - (2 / 5) * e - 2 * bandShift),
   1 + epsilon * (1 / 2 - bandShift),
   2 - epsilon * (e + bandShift),
   2 - 2 * epsilon * (e + bandShift),
   1]
end ThreeSum.Parameters


