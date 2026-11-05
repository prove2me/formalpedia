-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:05:12.647198+00:00
-- url     : https://prove2.me/theorems/3def588e-488d-4849-925a-e3310ef1bd12
-- title:
--   GlobalParameters
-- statement:
--   Definitions and structural lemmas for GlobalParameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalParameters.lean

import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def pi0 : ℝ := (406027953884819/500000000000000 : ℝ)
def pi1 : ℝ := (39662773613067/250000000000000 : ℝ)
def pi2 : ℝ := (14646498889047/500000000000000 : ℝ)
def alpha0 : ℝ := (90114578758847/100000000000000 : ℝ)
def alpha1 : ℝ := (5568117488677/62500000000000 : ℝ)
def alpha2 : ℝ := (4882166296349/500000000000000 : ℝ)
def deficit : ℝ := (134483535964511/10000000000000000 : ℝ)
def cutSlope : ℝ := (2790453661435908961/10000000000000000 : ℝ)
def dropSlope : ℝ := (184107960735415559/10000000000000000 : ℝ)
def y : ℝ := WeightedCacheParameters_e1ae71d.yRoot
def z : ℝ := WeightedCacheParameters_e1ae71d.zRoot
def three : ℝ := 3
def mean : ℝ := pi1+2*pi2
def bankArg : ℝ := 1+y^1369+y^2740
def queryArg1 : ℝ := 1+z^1369
def queryArg2 : ℝ := 1+z^1371+z^2740
def Hpi : ℝ := WeightedCacheParameters_e1ae71d.Hn/Real.log 2
def Halpha : ℝ := WeightedCacheParameters_e1ae71d.An/Real.log 2
def partitionEntropy : ℝ := WeightedCacheParameters_e1ae71d.Gn/Real.log 2
def bankEntropy : ℝ := WeightedCacheParameters_e1ae71d.Bn/Real.log 2
def queryEntropy : ℝ := WeightedCacheParameters_e1ae71d.Qn/Real.log 2
def certificateExponent : ℝ := 2400349260231/1250000000000
def targetExponent : ℝ := 384055881637/200000000000
def costLedger : List ℝ :=
  [2 * bankEntropy / Hpi,
   2 - partitionEntropy / Hpi + 2 * queryEntropy / Hpi,
   2 * Halpha / Hpi,
   1 + partitionEntropy / Hpi,
   2 - partitionEntropy / Hpi,
   1]
end ThreeSum.WeightedGlobalParameters
end
end WeightedCache3SUMRefinement_e1ae71d


