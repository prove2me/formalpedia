-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryParameters
-- name    : Submission_ThreeSum_TernaryParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:36.915211+00:00
-- url     : https://prove2.me/theorems/a8caf175-09c2-4489-a9d2-2ee682e0a105
-- title:
--   Ternary Parameters
-- statement:
--   Definitions and structural lemmas for Ternary Parameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
def pi0 : ℝ := (40602373 / 50000000 : ℝ)
def pi1 : ℝ := (317209 / 2000000 : ℝ)
def pi2 : ℝ := (733701 / 25000000 : ℝ)
def alpha0 : ℝ := (90113239 / 100000000 : ℝ)
def alpha1 : ℝ := (8908493 / 100000000 : ℝ)
def alpha2 : ℝ := (978268 / 100000000 : ℝ)
def three : ℝ := 3
def y : ℝ := (1816256201 / 10000000000 : ℝ)
def bankArg : ℝ := (121461348597670952401 / 100000000000000000000 : ℝ)
def z : ℝ := (752397677 / 10000000000 : ℝ)
def queryArg1 : ℝ := (10752397677 / 10000000000 : ℝ)
def queryArg2 : ℝ := (108090079034354996329 / 100000000000000000000 : ℝ)
def deficit : ℝ := (1344861 / 100000000 : ℝ)
def mean : ℝ := pi1 + 2 * pi2
def certificateExponent : ℝ := 9601397143994562657/5000000000000000000
def targetExponent : ℝ := 4800698571997281331/2500000000000000000
def Hpi : ℝ := (-pi0 * Real.log pi0 - pi1 * Real.log pi1 -
  pi2 * Real.log pi2) / Real.log 2
def Halpha : ℝ := (-alpha0 * Real.log alpha0 - alpha1 * Real.log alpha1 -
  alpha2 * Real.log alpha2) / Real.log 2
def partitionEntropy : ℝ := (pi1 * Real.log 2 + pi2 * Real.log three) / Real.log 2
def bankEntropy : ℝ := (Real.log bankArg - (mean - deficit) * Real.log y) / Real.log 2
def queryEntropy : ℝ := (pi1 * Real.log queryArg1 + pi2 * Real.log queryArg2 -
  deficit * Real.log z) / Real.log 2
def normalized_pi0 : ℝ := (40602373 / 25000000 : ℝ)
def normalized_pi1 : ℝ := (317209 / 250000 : ℝ)
def normalized_pi2 : ℝ := (733701 / 390625 : ℝ)
def normalized_alpha0 : ℝ := (90113239 / 50000000 : ℝ)
def normalized_alpha1 : ℝ := (8908493 / 6250000 : ℝ)
def normalized_alpha2 : ℝ := (489134 / 390625 : ℝ)
def normalized_three : ℝ := (3 / 2 : ℝ)
def normalized_y : ℝ := (1816256201 / 1250000000 : ℝ)
def normalized_z : ℝ := (752397677 / 625000000 : ℝ)
def costLedger : List ℝ :=
  [2 * bankEntropy / Hpi,
   2 - partitionEntropy / Hpi + 2 * queryEntropy / Hpi,
   2 * Halpha / Hpi,
   1 + partitionEntropy / Hpi,
   2 - partitionEntropy / Hpi,
   1]
end ThreeSum.TernaryParameters


