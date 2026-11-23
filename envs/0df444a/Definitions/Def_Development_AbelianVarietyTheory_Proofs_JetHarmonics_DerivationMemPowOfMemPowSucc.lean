-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DerivationMemPowOfMemPowSucc
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_DerivationMemPowOfMemPowSucc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:53.54844+00:00
-- url     : https://prove2.me/theorems/559e45d6-afb3-4edc-9ebd-63ff11981a5a
-- title:
--   Derivation Mem Pow Of Mem Pow Succ
-- statement:
--   Definitions and structural lemmas for Derivation Mem Pow Of Mem Pow Succ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DerivationMemPowOfMemPowSucc.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.DerivationMemPow
theorem derivation_mem_pow_of_mem_pow_succ {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
    (D : Derivation k A A) (I : Ideal A) (n : ℕ) :
    ∀ x ∈ I ^ (n + (1 : ℕ)), (D : A → A) x ∈ I ^ n := by
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ ?_ ?_
      · exact Ideal.mul_mem_right _ _ ha
      · have h := Ideal.mul_mem_mul hb (ih a ha)
        rwa [← pow_succ'] at h
    · intro y z hy hz
      rw [map_add]
      exact Ideal.add_mem _ hy hz
example : ∀ {k A : Type} [inst : CommRing k] [inst_1 : CommRing A] [inst_2 : Algebra k A] (D : Derivation k A A) (I : Ideal A) (n : ℕ), ∀ x ∈ I ^ (n + (1 : ℕ)), (D : A → A) x ∈ I ^ n :=
  fun D I n => derivation_mem_pow_of_mem_pow_succ D I n
end GlobalTheory.DerivationMemPow


