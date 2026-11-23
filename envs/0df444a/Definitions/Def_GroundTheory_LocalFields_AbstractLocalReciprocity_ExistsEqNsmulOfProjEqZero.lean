-- Prove2me | Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
-- name    : GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:48.399885+00:00
-- url     : https://prove2.me/theorems/2556067a-b146-48b8-9ee0-4e77d4211ff5
-- title:
--   Exists Eq Nsmul Of Proj Eq Zero
-- statement:
--   Definitions and structural lemmas for Exists Eq Nsmul Of Proj Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsEqNsmulOfProjEqZero.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_castHom_proj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField.Abstract
namespace ProfiniteInteger
def multiples (n : ℕ) : AddSubgroup ℤ̂ :=
  (AddMonoidHom.mulLeft (n : ℤ̂)).range
theorem proj_eq_val_cast {n k : ℕ+} (h : (n : ℕ) ∣ k) (x : ℤ̂) :
    proj n x = ((proj k x).val : ZMod n) := by
  rw [← castHom_proj h x, ZMod.castHom_apply, ZMod.cast_eq_val]
theorem eq_zero_of_nsmul_eq_zero {n : ℕ} (hn : n ≠ 0) {x : ℤ̂} (h : n • x = 0) : x = 0 := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ+, (N : ℕ) = n := ⟨⟨n, Nat.pos_of_ne_zero hn⟩, rfl⟩
  ext m
  rw [map_zero, proj_eq_val_cast (n := m) (k := N * m) (by simp) x, ZMod.natCast_eq_zero_iff]
  have h' := congrArg (proj (N * m)) h
  rw [map_nsmul, map_zero, nsmul_eq_mul] at h'
  have h'' : (((N : ℕ) * (proj (N * m) x).val : ℕ) : ZMod ((N * m : ℕ+) : ℕ)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact h'
  rw [ZMod.natCast_eq_zero_iff] at h''
  have h3 : (N : ℕ) * m ∣ (N : ℕ) * (proj (N * m) x).val := by
    rw [← PNat.mul_coe]
    exact h''
  exact Nat.dvd_of_mul_dvd_mul_left N.pos h3
instance : IsAddTorsionFree ℤ̂ where
  nsmul_right_injective n hn x y h := by
    rw [← sub_eq_zero]
    apply eq_zero_of_nsmul_eq_zero hn
    simp only at h
    rw [nsmul_sub, h, sub_self]
end ProfiniteInteger
end GroundTheory.LocalField.Abstract


