-- Prove2me | Definitions.Def_ThreeSum1960614_ModelWitnessPoints
-- name    : ThreeSum1960614_ModelWitnessPoints
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-14T13:33:21.8403+00:00
-- url     : https://prove2.me/theorems/311d6314-9ff3-44cf-917a-63bf97db1afa
-- title:
--   Rational ratio evaluation point for the model lower bound
-- statement:
--   The exact rational evaluation point $$u=\frac{859960785302793}{5000000000000000}$$ used to force a lower bound on the ratio parameter in the expansion-232 analytic model. This definition states no logarithmic or entropy inequality; those are separate proof obligations.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ModelWitnessLogs.lean#L12-L12

import Definitions.Def_ThreeSum1960614_FixedModelAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
open scoped BigOperators

noncomputable section
namespace ThreeSum1960614.FixedModel

def ratioPoint : ℝ := 859960785302793/5000000000000000







end ThreeSum1960614.FixedModel


