-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CollisionConstant
-- name    : OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CollisionConstant
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-09T13:37:40.781345+00:00
-- url     : https://prove2.me/theorems/e2fb211d-ec5e-4e02-8107-f1abdd9dcaf4
-- title:
--   Collision constant and its positivity
-- statement:
--   Define the collision constant as log(2)/4. This real constant is strictly positive.
--
--   This provider supplies only the positive numerical constant used by later collision bounds; it does not establish the determinant-contradiction argument.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/DeterminantContradiction.lean#L15-L19

import Mathlib

namespace OAI

open Filter
open scoped Topology

namespace PiExponent.DeterminantContradiction

noncomputable def collisionConstant : ℝ := Real.log 2 / 4

theorem collisionConstant_pos : 0 < collisionConstant := by
  unfold collisionConstant
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

end PiExponent.DeterminantContradiction

end OAI


