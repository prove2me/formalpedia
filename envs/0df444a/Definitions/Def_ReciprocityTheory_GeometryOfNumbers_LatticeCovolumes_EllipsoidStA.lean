-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_EllipsoidStA
-- name    : ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_EllipsoidStA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:12.26119+00:00
-- url     : https://prove2.me/theorems/4a739a0f-61a1-483c-9b37-87831ef08f50
-- title:
--   Ellipsoid St A
-- statement:
--   Definitions and structural lemmas for Ellipsoid St A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/EllipsoidStA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
open MeasureTheory
section Generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def sqBall (r : ℕ) (E : Type*) [NormedAddCommGroup E] (R : ℝ) : Set (Fin r → E) :=
  {u | ∑ k, ‖u k‖ ^ 2 ≤ R ^ 2}
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace V] [BorelSpace V]
end Generic
end ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall


