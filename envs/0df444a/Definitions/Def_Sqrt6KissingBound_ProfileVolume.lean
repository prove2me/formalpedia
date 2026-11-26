-- Prove2me | Definitions.Def_Sqrt6KissingBound_ProfileVolume
-- name    : Sqrt6KissingBound_ProfileVolume
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:02:51.954646+00:00
-- url     : https://prove2.me/theorems/89fc2634-2820-4518-99db-388c2f5c101e
-- title:
--   Profile Volume
-- statement:
--   Definitions and structural lemmas for Profile Volume, from Sébastien Palcoux (sebastienpalcoux/sqrt6-kissing-bound; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned The universal square-root-of-six exponential base bound for Euclidean kissing numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileVolume.lean

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
set_option autoImplicit true
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
def tailBall (d : ℕ) (r : ℝ) : Set (Fin d → ℝ) :=
  (@WithLp.toLp 2 (Fin d → ℝ)) ⁻¹'
    ball (0 : EuclideanSpace ℝ (Fin d)) r
def profileRegion (d : ℕ) (s : Set ℝ) (g : ℝ → ℝ) :
    Set (ℝ × (Fin d → ℝ)) :=
  {p | p.1 ∈ s ∧ p.2 ∈ tailBall d (g p.1)}
def rotationalProfile (d : ℕ) (s : Set ℝ) (g : ℝ → ℝ) :
    Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  (standardCoordinates d).symm ⁻¹' profileRegion d s g
end
end Sqrt6KissingBound


