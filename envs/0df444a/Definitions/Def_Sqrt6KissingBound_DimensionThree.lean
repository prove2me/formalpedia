-- Prove2me | Definitions.Def_Sqrt6KissingBound_DimensionThree
-- name    : Sqrt6KissingBound_DimensionThree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:07:54.209714+00:00
-- url     : https://prove2.me/theorems/a13d686a-1ad7-4da9-a90c-b569f9063577
-- title:
--   Dimension Three
-- statement:
--   Definitions and structural lemmas for Dimension Three, from Sébastien Palcoux (sebastienpalcoux/sqrt6-kissing-bound; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned The universal square-root-of-six exponential base bound for Euclidean kissing numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionThree.lean

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
set_option autoImplicit true
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
abbrev s3_d3 : ℝ := Real.sqrt 3
abbrev a_d3 : ℝ := s3_d3 / 2
def upperProfile3 (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 2)
def upperBody3 : Set (EuclideanSpace ℝ (Fin 3)) :=
  rotationalProfile 2 (Set.Ioo a_d3 1) upperProfile3
def standardBody3 : Set (EuclideanSpace ℝ (Fin 3)) :=
  lowerBicone 1 ∪ upperBody3
end
end Sqrt6KissingBound


