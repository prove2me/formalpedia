-- Prove2me | Definitions.Def_Sqrt6KissingBound_ProfileIntegral
-- name    : Sqrt6KissingBound_ProfileIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:03:39.825344+00:00
-- url     : https://prove2.me/theorems/561486de-f027-4da7-901b-9ba851e732e2
-- title:
--   Profile Integral
-- statement:
--   Definitions and structural lemmas for Profile Integral, from Sébastien Palcoux (sebastienpalcoux/sqrt6-kissing-bound; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned The universal square-root-of-six exponential base bound for Euclidean kissing numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileIntegral.lean

import Definitions.Def_Sqrt6KissingBound_ProfileVolume
set_option autoImplicit true
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped ENNReal Interval Real
def unitBallVolume (d : ℕ) : ℝ≥0∞ :=
  (volume : Measure (EuclideanSpace ℝ (Fin d))) (ball 0 1)
end
end Sqrt6KissingBound


