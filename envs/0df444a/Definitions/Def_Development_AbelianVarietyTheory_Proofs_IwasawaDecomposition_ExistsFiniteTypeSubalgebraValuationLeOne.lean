-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFiniteTypeSubalgebraValuationLeOne
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFiniteTypeSubalgebraValuationLeOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:27.257795+00:00
-- url     : https://prove2.me/theorems/e72df153-de6e-443a-a58a-ff9a31e3f42d
-- title:
--   Exists Finite Type Subalgebra Valuation Le One
-- statement:
--   Definitions and structural lemmas for Exists Finite Type Subalgebra Valuation Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFiniteTypeSubalgebraValuationLeOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.FractionalParts
def fracs {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (C : Subalgebra A B) :
    Subalgebra A B where
  carrier := {b | ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a}
  mul_mem' := by
    rintro x y ⟨a, ha, s, hs, hu, h⟩ ⟨a', ha', s', hs', hu', h'⟩
    exact ⟨a * a', C.mul_mem ha ha', s * s', C.mul_mem hs hs', hu.mul hu', by
      rw [← h, ← h']; ring⟩
  add_mem' := by
    rintro x y ⟨a, ha, s, hs, hu, h⟩ ⟨a', ha', s', hs', hu', h'⟩
    exact ⟨s' * a + s * a', C.add_mem (C.mul_mem hs' ha) (C.mul_mem hs ha'), s * s',
      C.mul_mem hs hs', hu.mul hu', by rw [← h, ← h']; ring⟩
  algebraMap_mem' r := ⟨algebraMap A B r, C.algebraMap_mem r, 1, C.one_mem, isUnit_one, one_mul _⟩
end GlobalTheory.FractionalParts


