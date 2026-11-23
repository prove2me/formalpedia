-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomLiftOfFormallySmooth
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomLiftOfFormallySmooth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:45.53375+00:00
-- url     : https://prove2.me/theorems/dee00993-c8a2-41c7-893b-807e1bdfd3d5
-- title:
--   Exists Ring Hom Lift Of Formally Smooth
-- statement:
--   Definitions and structural lemmas for Exists Ring Hom Lift Of Formally Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRingHomLiftOfFormallySmooth.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DI
def powModP (p : ℕ) (hp : p.Prime) (B : Type) [CommRing B] :
    B →+* B ⧸ Ideal.span {(p : B)} where
  toFun z := Ideal.Quotient.mk _ (z ^ p)
  map_one' := by simp
  map_mul' x y := by simp [mul_pow]
  map_zero' := by simp [zero_pow hp.ne_zero]
  map_add' x y := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp x y
    rw [hr, map_add, map_add]
    have : Ideal.Quotient.mk (Ideal.span {(p : B)}) ((p : B) * x * y * r) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, mul_assoc, mul_assoc]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [this, add_zero]
end GlobalTheory.DI


