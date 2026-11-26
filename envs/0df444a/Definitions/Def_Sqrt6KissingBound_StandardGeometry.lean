-- Prove2me | Definitions.Def_Sqrt6KissingBound_StandardGeometry
-- name    : Sqrt6KissingBound_StandardGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:02:47.046537+00:00
-- url     : https://prove2.me/theorems/bdccaef0-707a-470c-b221-fd032106e960
-- title:
--   Standard Geometry
-- statement:
--   Definitions and structural lemmas for Standard Geometry, from Sébastien Palcoux (sebastienpalcoux/sqrt6-kissing-bound; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned The universal square-root-of-six exponential base bound for Euclidean kissing numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/StandardGeometry.lean

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_Geometry
import Mathlib.Analysis.InnerProductSpace.PiL2
set_option autoImplicit true
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
def standardAxis (d : ℕ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  standardCoordinates d (1, 0)
end
end Sqrt6KissingBound


