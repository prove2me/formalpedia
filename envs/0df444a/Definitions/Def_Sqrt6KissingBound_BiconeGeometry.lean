-- Prove2me | Definitions.Def_Sqrt6KissingBound_BiconeGeometry
-- name    : Sqrt6KissingBound_BiconeGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:03:39.607958+00:00
-- url     : https://prove2.me/theorems/ed72051f-b111-4174-8338-ee4431c29250
-- title:
--   Bicone Geometry
-- statement:
--   Definitions and structural lemmas for Bicone Geometry, from Sébastien Palcoux (sebastienpalcoux/sqrt6-kissing-bound; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned The universal square-root-of-six exponential base bound for Euclidean kissing numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeGeometry.lean

import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
set_option autoImplicit true
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
abbrev s3_bg : ℝ := Real.sqrt 3
abbrev a_bg : ℝ := s3_bg / 2
abbrev upperSlope_bg : ℝ := 2 + s3_bg
def lowerBicone (k : ℕ) : Set (EuclideanSpace ℝ (Fin (k + 2))) :=
  rotationalProfile (k + 1) (Set.Ioo 0 a_bg) (fun t => t / s3_bg)
def upperBicone (k : ℕ) : Set (EuclideanSpace ℝ (Fin (k + 2))) :=
  rotationalProfile (k + 1) (Set.Ioo a_bg 1) (fun t => upperSlope_bg * (1 - t))
def standardBicone (k : ℕ) : Set (EuclideanSpace ℝ (Fin (k + 2))) :=
  lowerBicone k ∪ upperBicone k
end
end Sqrt6KissingBound


