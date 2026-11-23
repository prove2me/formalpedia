-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSabMapOfBaseEq
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSabMapOfBaseEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:23:09.263032+00:00
-- url     : https://prove2.me/theorems/bcf46d91-efca-4322-957d-247f908898b6
-- title:
--   Exists Sab Map Of Base Eq
-- statement:
--   Definitions and structural lemmas for Exists Sab Map Of Base Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSabMapOfBaseEq.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory
theorem zeta_eq_pow_div_of_dvd {a b : ℕ} (hb : 0 < b) (h : a ∣ b) : zeta a = zeta b ^ (b / a) := by
  obtain ⟨c, rfl⟩ := h
  have ha : 0 < a := Nat.pos_of_mul_pos_right hb
  have hc : 0 < c := Nat.pos_of_mul_pos_left hb
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  rw [Nat.mul_div_cancel_left c ha, zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp
theorem levelField_le_of_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : KA l ≤ KA l₂ := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rcases hx with rfl | hx
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [zeta_eq_pow_div_of_dvd l₂.A_pos h]
    exact pow_mem (IntermediateField.subset_adjoin ℚ ({H.rt0, zeta l₂.A} : Set ℂ) (by simp)) _
def baseOfFinerLevel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : Base l (KA l₂) where
  unit := (baseKA l₂).unit
  ρ := (baseKA l₂).ρ
  ρ_sq := (baseKA l₂).ρ_sq
  ζ := IntermediateField.inclusion (levelField_le_of_dvd h) (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective (IntermediateField.inclusion_injective (levelField_le_of_dvd h))
def levelFieldIncl {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : KA l →+* KA l₂ :=
  (IntermediateField.inclusion (levelField_le_of_dvd h)).toRingHom
end GlobalTheory


