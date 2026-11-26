-- Prove2me | Definitions.Def_Sqrt6KissingBound_CoordinateVolume
-- name    : Sqrt6KissingBound_CoordinateVolume
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:02:23.292017+00:00
-- url     : https://prove2.me/theorems/05057cb8-d929-4156-8fd1-1095a7b0a7e4
-- title:
--   Coordinate Volume
-- statement:
--   Definitions and structural lemmas for Coordinate Volume, from Sébastien Palcoux (sebastienpalcoux/sqrt6-kissing-bound; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned The universal square-root-of-six exponential base bound for Euclidean kissing numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CoordinateVolume.lean

import Mathlib
set_option autoImplicit true
namespace Sqrt6KissingBound
noncomputable section
open MeasureTheory
noncomputable def standardCoordinates (d : ℕ) :
    (ℝ × (Fin d → ℝ)) ≃ᵐ EuclideanSpace ℝ (Fin (d + 1)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm.trans
    (MeasurableEquiv.toLp 2 _)
end
end Sqrt6KissingBound


