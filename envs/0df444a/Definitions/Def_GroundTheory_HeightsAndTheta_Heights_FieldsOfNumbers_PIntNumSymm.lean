-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:18.60159+00:00
-- url     : https://prove2.me/theorems/18207b23-bb71-43b3-8733-6c53bae44559
-- title:
--   PInt Num Symm
-- statement:
--   Definitions and structural lemmas for PInt Num Symm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumSymm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open GroundTheory.Heights₂.Heights.NumbersDVR
section
variable {K : Type*}
theorem diffStep_comm (a b : K → ℤ) (h : (K → ℤ) → ℤ) :
    diffStep a (diffStep b h) = diffStep b (diffStep a h) := by
  funext m
  simp only [diffStep, sub_sub, add_comm a b]
  ring
instance diffStep_leftCommutative :
    LeftCommutative (diffStep : (K → ℤ) → ((K → ℤ) → ℤ) → (K → ℤ) → ℤ) :=
  ⟨diffStep_comm⟩
end
end GroundTheory.Heights₂.Heights.FieldNumbers


