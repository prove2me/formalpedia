-- Prove2me | Definitions.Def_Sqrt6KissingBound_KissingBound
-- name    : Sqrt6KissingBound_KissingBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:08:31.348805+00:00
-- url     : https://prove2.me/theorems/90011012-921f-5fb9-a657-39f11678dbb0
-- title:
--   Kissing Bound
-- statement:
--   Definitions and structural lemmas for Kissing Bound, from Sébastien Palcoux (sebastienpalcoux/sqrt6-kissing-bound; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned The universal square-root-of-six exponential base bound for Euclidean kissing numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/KissingBound.lean

import Definitions.Def_Sqrt6KissingBound_DimensionOne
import Definitions.Def_Sqrt6KissingBound_DimensionThree
import Definitions.Def_Sqrt6KissingBound_DimensionFour
import Definitions.Def_Sqrt6KissingBound_BiconeBounds
set_option autoImplicit true
namespace Sqrt6KissingBound
noncomputable section
def IsKissingConfiguration {n : ℕ}
    (X : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  (∀ x ∈ X, ‖x‖ = 1) ∧
    (∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2)
end
end Sqrt6KissingBound


