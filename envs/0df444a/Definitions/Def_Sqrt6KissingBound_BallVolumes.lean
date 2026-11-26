-- Prove2me | Definitions.Def_Sqrt6KissingBound_BallVolumes
-- name    : Sqrt6KissingBound_BallVolumes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:05:01.229608+00:00
-- url     : https://prove2.me/theorems/35b7e9f7-7a23-5c70-a331-ac30170ce667
-- title:
--   Ball Volumes
-- statement:
--   Definitions and structural lemmas for Ball Volumes, from Sébastien Palcoux (sebastienpalcoux/sqrt6-kissing-bound; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned The universal square-root-of-six exponential base bound for Euclidean kissing numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BallVolumes.lean

import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
set_option autoImplicit true
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Real
end
end Sqrt6KissingBound


