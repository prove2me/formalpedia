-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_QuadraticFields_SqfField
-- name    : GroundTheory_HeightsAndTheta_Heights_QuadraticFields_SqfField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:53.177108+00:00
-- url     : https://prove2.me/theorems/289f5321-e034-4843-8d29-285a2b305f71
-- title:
--   Sqf Field
-- statement:
--   Definitions and structural lemmas for Sqf Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/QuadraticFields/SqfField.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_IndefiniteTreeX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Rows
noncomputable section
instance sqfField_fact_noRoot (d : ℕ) [NeZero d] : Fact (∀ r : ℚ, r ^ 2 ≠ -(d : ℚ) + 0 * r) :=
  ⟨fun r h ↦ by
    have hd : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    rw [zero_mul, add_zero] at h
    nlinarith [sq_nonneg r]⟩
abbrev SqfField (d : ℕ) : Type := QuadraticAlgebra ℚ (-(d : ℚ)) 0
instance (d : ℕ) [NeZero d] : NumberField (SqfField d) := {}
instance (d : ℕ) [NeZero d] : Algebra.IsQuadraticExtension ℚ (SqfField d) :=
  ⟨QuadraticAlgebra.finrank_eq_two _ _⟩
def sqrtNegD (d : ℕ) : SqfField d := ⟨0, 1⟩
end
end GroundTheory.Heights₂.Heights.Rows


