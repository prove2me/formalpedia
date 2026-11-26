-- Prove2me | Definitions.Def_Sqrt6KissingBound_Geometry
-- name    : Sqrt6KissingBound_Geometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:02:20.054935+00:00
-- url     : https://prove2.me/theorems/06d58da6-89d9-5e02-b477-eec02fce5cf2
-- title:
--   Geometry
-- statement:
--   Definitions and structural lemmas for Geometry, from Sébastien Palcoux (sebastienpalcoux/sqrt6-kissing-bound; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned The universal square-root-of-six exponential base bound for Euclidean kissing numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/Geometry.lean

import Mathlib
set_option autoImplicit true
namespace Sqrt6KissingBound
noncomputable section
open Set
open NormedSpace
abbrev s3 : ℝ := Real.sqrt 3
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def strictCone (x : E) : Set E :=
  {y | (s3 / 2) * ‖y‖ < inner ℝ x y}
end
end Sqrt6KissingBound


