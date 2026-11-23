-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenVal
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:09.346829+00:00
-- url     : https://prove2.me/theorems/e3bd94ee-1265-41b7-b3e0-4e7b42dbf6cd
-- title:
--   Theta Gen Val
-- statement:
--   Definitions and structural lemmas for Theta Gen Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenVal.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasVal_of_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasVal_unique

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
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.DVR
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
lemma hasVal_mul {c d : FractionRing V} {n m : ℤ} (hc : HasVal ϖ c n) (hd : HasVal ϖ d m) (hϖ : Irreducible ϖ) :
    HasVal ϖ (c * d) (n + m) := by
  obtain ⟨u, hu⟩ := hc
  obtain ⟨w, hw⟩ := hd
  have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
  refine ⟨u * w, ?_⟩
  rw [hu, hw, zpow_add₀ hπ, Units.val_mul, map_mul]
  ring
open scoped Classical in

def valE (hϖ : Irreducible ϖ) (c : FractionRing V) : ℤ :=
  if h : c = 0 then 0 else (hasVal_of_ne_zero hϖ h).choose
lemma hasVal_valE (hϖ : Irreducible ϖ) {c : FractionRing V} (hc : c ≠ 0) : HasVal ϖ c (valE hϖ c) := by
  unfold valE
  rw [dif_neg hc]
  exact (hasVal_of_ne_zero hϖ hc).choose_spec
open scoped Classical in

def vK (hϖ : Irreducible ϖ) : AddValuation (FractionRing V) (WithTop ℚ) :=
  AddValuation.of (fun c => if c = 0 then ⊤ else ((valE hϖ c : ℚ) : WithTop ℚ))
    (by simp)
    (by
      have h1 : HasVal ϖ (1 : FractionRing V) 0 := ⟨1, by simp⟩
      simp [hasVal_unique hϖ (hasVal_valE hϖ one_ne_zero) h1])
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      by_cases hxy : x + y = 0
      · simp [hxy]
      simp only [hx, hy, hxy, if_false]
      have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
      have key : ∀ {a b : FractionRing V}, a ≠ 0 → b ≠ 0 → a + b ≠ 0 → valE hϖ a ≤ valE hϖ b →
          valE hϖ a ≤ valE hϖ (a + b) := by
        intro a b ha hb hab hle
        have hva := hasVal_valE hϖ ha
        have hvb := hasVal_valE hϖ hb
        have hvab := hasVal_valE hϖ hab
        generalize valE hϖ a = na at hva hle ⊢
        generalize valE hϖ b = nb at hvb hle
        generalize valE hϖ (a + b) = nab at hvab ⊢
        obtain ⟨u, hu⟩ := hva
        obtain ⟨w, hw⟩ := hvb
        obtain ⟨d, hd⟩ : ∃ d : ℕ, nb = na + d := ⟨(nb - na).toNat, by omega⟩
        set r : V := (u : V) + ϖ ^ d * (w : V)
        have hab' : a + b = algebraMap V (FractionRing V) ϖ ^ na * algebraMap V (FractionRing V) r := by
          rw [hu, hw, hd, zpow_add₀ hπ, zpow_natCast]
          simp only [r, map_add, map_mul, map_pow]
          ring
        have hr : r ≠ 0 := by
          rintro h0
          apply hab
          rw [hab', h0, map_zero, mul_zero]
        obtain ⟨k, z, hz⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
        have hv : HasVal ϖ (a + b) (na + k) :=
          ⟨z, by rw [hab', hz, zpow_add₀ hπ, zpow_natCast, map_mul, map_pow]; ring⟩
        rw [hasVal_unique hϖ hvab hv]
        omega
      rcases le_total (valE hϖ x) (valE hϖ y) with h | h
      · have := key hx hy hxy h
        exact min_le_of_left_le (by exact_mod_cast this)
      · have := key hy hx (by rwa [add_comm]) h
        rw [add_comm] at this
        exact min_le_of_right_le (by exact_mod_cast this))
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      have hxy : x * y ≠ 0 := mul_ne_zero hx hy
      simp only [hx, hy, hxy, if_false]
      rw [hasVal_unique hϖ (hasVal_valE hϖ hxy) (hasVal_mul (hasVal_valE hϖ hx) (hasVal_valE hϖ hy) hϖ)]
      push_cast
      rfl)
end ReciprocityTheory.ChartRestriction.G.DVR.TG


