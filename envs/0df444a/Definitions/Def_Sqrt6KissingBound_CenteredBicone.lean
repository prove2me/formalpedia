-- Prove2me | Definitions.Def_Sqrt6KissingBound_CenteredBicone
-- name    : Sqrt6KissingBound_CenteredBicone
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:06:10.47144+00:00
-- url     : https://prove2.me/theorems/edbf7f2a-582e-5af9-8b05-17ecb49de171
-- title:
--   Centered Bicone
-- statement:
--   Definitions and structural lemmas for Centered Bicone, from Sébastien Palcoux (sebastienpalcoux/sqrt6-kissing-bound; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned The universal square-root-of-six exponential base bound for Euclidean kissing numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBicone.lean

import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Definitions.Def_Sqrt6KissingBound_VolumePacking
set_option autoImplicit true
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
def axisTo (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 2))) :
    EuclideanSpace ℝ (Fin (k + 2)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (k + 2)) :=
  Submodule.reflection (ℝ ∙ (standardAxis (k + 1) - x))ᗮ
def centeredBicone (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 2))) :
    Set (EuclideanSpace ℝ (Fin (k + 2))) :=
  (axisTo k x).symm ⁻¹' standardBicone k
end
end Sqrt6KissingBound


