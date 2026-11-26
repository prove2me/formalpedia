-- Prove2me | Definitions.Def_Sqrt6KissingBound_DimensionFour
-- name    : Sqrt6KissingBound_DimensionFour
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:07:27.571831+00:00
-- url     : https://prove2.me/theorems/47482809-2e69-4a9b-9005-75138c696a8a
-- title:
--   Dimension Four
-- statement:
--   Definitions and structural lemmas for Dimension Four, from Sébastien Palcoux (sebastienpalcoux/sqrt6-kissing-bound; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned The universal square-root-of-six exponential base bound for Euclidean kissing numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
set_option autoImplicit true
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
abbrev s3_d4 : ℝ := Real.sqrt 3
abbrev a_d4 : ℝ := s3_d4 / 2
def upperProfile4 (t : ℝ) : ℝ := (1 - t) * (14 * t + 2 - 6 * s3_d4)
def upperBody4 : Set (EuclideanSpace ℝ (Fin 4)) :=
  rotationalProfile 3 (Set.Ioo a_d4 1) upperProfile4
def standardBody4 : Set (EuclideanSpace ℝ (Fin 4)) := lowerBicone 2 ∪ upperBody4
end
end Sqrt6KissingBound


