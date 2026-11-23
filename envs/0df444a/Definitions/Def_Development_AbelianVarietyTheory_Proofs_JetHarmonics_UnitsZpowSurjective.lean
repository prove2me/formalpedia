-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitsZpowSurjective
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitsZpowSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:58.022469+00:00
-- url     : https://prove2.me/theorems/11066f57-39dc-4c94-a550-1756fd605dc4
-- title:
--   Units Zpow Surjective
-- statement:
--   Definitions and structural lemmas for Units Zpow Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitsZpowSurjective.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.DivisibleUnits
theorem units_zpow_surjective {F : Type} [Field F] [IsAlgClosed F] {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun a : Fˣ => a ^ n) := by
  have nat_root : ∀ (m : ℕ), 0 < m → ∀ x : Fˣ, ∃ y : Fˣ, y ^ m = x := by
    intro m hm x
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : F) hm
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne'] at hz
      exact x.ne_zero hz.symm
    refine ⟨Units.mk0 z hz0, ?_⟩
    ext
    simp [hz]
  intro x
  rcases Int.lt_or_gt_of_ne hn with h | h
  · obtain ⟨y, hy⟩ := nat_root n.natAbs (Int.natAbs_pos.mpr hn) x⁻¹
    refine ⟨y, ?_⟩
    show y ^ n = x
    have : n = -(n.natAbs : ℤ) := by omega
    rw [this, zpow_neg, zpow_natCast, hy, inv_inv]
  · obtain ⟨y, hy⟩ := nat_root n.natAbs (Int.natAbs_pos.mpr hn) x
    refine ⟨y, ?_⟩
    show y ^ n = x
    have : n = (n.natAbs : ℤ) := by omega
    rw [this, zpow_natCast, hy]
noncomputable def divisibleUnits (F : Type) [Field F] [IsAlgClosed F] :
    DivisibleBy (Additive Fˣ) ℤ :=
  divisibleByOfSMulRightSurj (Additive Fˣ) ℤ (fun {n} hn x => by
    obtain ⟨y, hy⟩ := units_zpow_surjective (F := F) hn (Additive.toMul x)
    exact ⟨Additive.ofMul y, by simpa using congrArg Additive.ofMul hy⟩)
end GlobalTheory.DivisibleUnits


