-- Prove2me | Definitions.Def_Sqrt6KissingBound_CenteredBody
-- name    : Sqrt6KissingBound_CenteredBody
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:06:39.604202+00:00
-- url     : https://prove2.me/theorems/fd2fd131-3d04-5102-ae83-771c20c23329
-- title:
--   Centered Body
-- statement:
--   Definitions and structural lemmas for Centered Body, from Sébastien Palcoux (sebastienpalcoux/sqrt6-kissing-bound; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned The universal square-root-of-six exponential base bound for Euclidean kissing numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBody.lean

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
set_option autoImplicit true
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
def centeredBody (k : ℕ) (S : Set (EuclideanSpace ℝ (Fin (k + 2))))
    (x : EuclideanSpace ℝ (Fin (k + 2))) :
    Set (EuclideanSpace ℝ (Fin (k + 2))) :=
  (axisTo k x).symm ⁻¹' S
end
end Sqrt6KissingBound


