-- Prove2me | Definitions.Def_Sqrt6KissingBound_BiconeVolume
-- name    : Sqrt6KissingBound_BiconeVolume
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:05:33.590907+00:00
-- url     : https://prove2.me/theorems/94299dea-6652-45a8-8dd9-81cc924b1c74
-- title:
--   Bicone Volume
-- statement:
--   Definitions and structural lemmas for Bicone Volume, from Sébastien Palcoux (sebastienpalcoux/sqrt6-kissing-bound; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned The universal square-root-of-six exponential base bound for Euclidean kissing numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeVolume.lean

import Definitions.Def_Sqrt6KissingBound_BodyVolumeAdditivity
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
import Definitions.Def_Sqrt6KissingBound_LinearProfileIntegral
import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
set_option autoImplicit true
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
abbrev s3_bv : ℝ := Real.sqrt 3
abbrev a_bv : ℝ := s3_bv / 2
abbrev upperSlope_bv : ℝ := 2 + s3_bv
end
end Sqrt6KissingBound


