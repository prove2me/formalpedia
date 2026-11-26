-- Prove2me | Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
-- name    : Sqrt6KissingBound_ProfileIntegralReal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:04:25.545795+00:00
-- url     : https://prove2.me/theorems/78bc40db-866e-4a5a-9b52-91c4c55c2bd8
-- title:
--   Profile Integral Real
-- statement:
--   Definitions and structural lemmas for Profile Integral Real, from Sébastien Palcoux (sebastienpalcoux/sqrt6-kissing-bound; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned The universal square-root-of-six exponential base bound for Euclidean kissing numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileIntegralReal.lean

import Definitions.Def_Sqrt6KissingBound_ProfileIntegral
import Mathlib.MeasureTheory.Measure.Real
set_option autoImplicit true
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped ENNReal Interval Real
def unitBallVolumeReal (d : ℕ) : ℝ :=
  (volume : Measure (EuclideanSpace ℝ (Fin d))).real (ball 0 1)
end
end Sqrt6KissingBound


