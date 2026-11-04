-- Prove2me | Definitions.Def_Submission_Weighted_GlobalParameters
-- name    : Submission_Weighted_GlobalParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:38.214007+00:00
-- url     : https://prove2.me/theorems/5ac679d4-742f-48b4-b251-456df197e34b
-- title:
--   Global Parameters
-- statement:
--   Definitions and structural lemmas for Global Parameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def pi0 : ℝ := (8120584037 / 10000000000 : ℝ)
def pi1 : ℝ := (198333677 / 1250000000 : ℝ)
def pi2 : ℝ := (292746547 / 10000000000 : ℝ)
def alpha0 : ℝ := (13517251391 / 15000000000 : ℝ)
def alpha1 : ℝ := (2672750671 / 30000000000 : ℝ)
def alpha2 : ℝ := (292746547 / 30000000000 : ℝ)
def deficit : ℝ := (134483020951 / 10000000000000 : ℝ)
def cutSlope : ℝ := (130448080617511 / 1250000000000 : ℝ)
def dropSlope : ℝ := (134483020951 / 19531250000 : ℝ)
def y : ℝ := WeightedCacheParameters.yRoot
def z : ℝ := WeightedCacheParameters.zRoot
def three : ℝ := 3
def mean : ℝ := pi1+2*pi2
def bankArg : ℝ := 1+y^512+y^1025
def queryArg1 : ℝ := 1+z^512
def queryArg2 : ℝ := 1+z^513+z^1025
def Hpi : ℝ := WeightedCacheParameters.Hn/Real.log 2
def Halpha : ℝ := WeightedCacheParameters.An/Real.log 2
def partitionEntropy : ℝ := WeightedCacheParameters.Gn/Real.log 2
def bankEntropy : ℝ := WeightedCacheParameters.Bn/Real.log 2
def queryEntropy : ℝ := WeightedCacheParameters.Qn/Real.log 2
def certificateExponent : ℝ := 480069853/250000000
def targetExponent : ℝ := 96013971/50000000
def costLedger : List ℝ :=
  [2 * bankEntropy / Hpi,
   2 - partitionEntropy / Hpi + 2 * queryEntropy / Hpi,
   2 * Halpha / Hpi,
   1 + partitionEntropy / Hpi,
   2 - partitionEntropy / Hpi,
   1]
end ThreeSum.WeightedGlobalParameters


