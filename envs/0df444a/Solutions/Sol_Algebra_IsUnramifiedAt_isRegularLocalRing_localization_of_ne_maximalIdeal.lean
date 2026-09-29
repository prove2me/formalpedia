-- Prove2me | solution 1 for Algebra.IsUnramifiedAt.isRegularLocalRing_localization_of_ne_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6c16769f-3713-58fa-9347-27b1bd7173d8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsUnramifiedAt_isRegularLocalRing_localization_of_ne_maximalIdeal

set_option autoImplicit false
set_option maxHeartbeats 800000

open TensorProduct

open IsLocalRing in
theorem solution
    {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsLocalRing R₀]
    (hR : ∀ (𝔯 : Ideal R₀) [𝔯.IsPrime], 𝔯 ≠ IsLocalRing.maximalIdeal R₀ →
      IsRegularLocalRing (Localization.AtPrime 𝔯))
    (hdim : ringKrullDim R₀ ≤ (2 : WithBot ℕ∞))
    (K₀ : Type*) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    {B : Type*} [CommRing B] [IsNoetherianRing B] [Algebra R₀ B] [Module.Finite R₀ B]
    (F : Type*) [CommRing F] [Algebra B F] [Algebra R₀ F] [Algebra K₀ F]
    [IsScalarTower R₀ B F] [IsScalarTower R₀ K₀ F]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)) F]
    (hinj : Function.Injective (algebraMap B F)) [IsReduced F]
    (hB : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], ¬ 𝔭.IsMaximal → Algebra.IsUnramifiedAt R₀ 𝔭) :
    ∀ (𝔭 : Ideal B) [𝔭.IsPrime], ¬ 𝔭.IsMaximal → IsRegularLocalRing (Localization.AtPrime 𝔭) := by
  intro 𝔭 _ hnm
  classical

  set 𝔯 : Ideal R₀ := 𝔭.under R₀ with h𝔯def
  haveI h𝔯p : 𝔯.IsPrime := Ideal.IsPrime.under R₀ 𝔭
  haveI : 𝔭.LiesOver 𝔯 := ⟨rfl⟩
  have h𝔯m : 𝔯 ≠ maximalIdeal R₀ := by
    intro h
    apply hnm
    have hmx : (𝔭.comap (algebraMap R₀ B)).IsMaximal := by
      show 𝔯.IsMaximal
      rw [h]
      exact IsLocalRing.maximalIdeal.isMaximal R₀
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap 𝔭 hmx

  have hAreg : IsRegularLocalRing (Localization.AtPrime 𝔯) := hR 𝔯 h𝔯m
  have hsA : (Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔯)) : WithBot ℕ∞) = 𝔯.height := by
    rw [hAreg.spanFinrank_maximalIdeal, IsLocalization.AtPrime.ringKrullDim_eq_height 𝔯 (Localization.AtPrime 𝔯)]
  have hsA' : (Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔯)) : ℕ∞) = 𝔯.height := by
    exact_mod_cast hsA
  have hht : 𝔯.height ≤ 1 := by
    have hlt : 𝔯 < maximalIdeal R₀ := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal h𝔯p.ne_top) h𝔯m
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have h2 : ((maximalIdeal R₀).height : WithBot ℕ∞) ≤ 2 := Ideal.height_le_ringKrullDim_of_isPrime.trans hdim
    have h2' : (maximalIdeal R₀).height ≤ 2 := WithBot.coe_le_coe.1 (by rw [WithBot.coe_ofNat]; exact h2)
    have h3 : 𝔯.height + 1 ≤ 2 := h1.trans h2'
    cases hq : 𝔯.height using ENat.recTopCoe with
    | top => rw [hq] at h3; simp at h3
    | coe n => rw [hq] at h3; norm_cast at h3 ⊢; omega

  letI : Algebra (Localization.AtPrime 𝔯) (Localization.AtPrime 𝔭) := Localization.AtPrime.algebraOfLiesOver 𝔯 𝔭
  have hunr : Algebra.IsUnramifiedAt R₀ 𝔭 := hB 𝔭 hnm
  have hmapeq : 𝔯.map (algebraMap R₀ (Localization.AtPrime 𝔭)) = maximalIdeal (Localization.AtPrime 𝔭) :=
    ((Algebra.isUnramifiedAt_iff_map_eq R₀ 𝔯 𝔭).1 hunr).2
  have hmapA : (maximalIdeal (Localization.AtPrime 𝔯)).map
      (algebraMap (Localization.AtPrime 𝔯) (Localization.AtPrime 𝔭)) = maximalIdeal (Localization.AtPrime 𝔭) := by
    rw [← hmapeq, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hs : Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔭)) ≤
      Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔯)) := by
    rw [← hmapA]
    exact Ideal.spanFinrank_map_le_of_fg _ (IsNoetherian.noetherian _)

  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (Localization.AtPrime 𝔭) ?_
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 (Localization.AtPrime 𝔭)]

  by_cases h0 : 𝔯 = ⊥
  ·
    have hq0 : 𝔯.height = 0 := by rw [h0]; exact Ideal.height_bot
    have hA0 : Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔯)) = 0 := by
      have h := hsA'
      rw [hq0] at h
      exact_mod_cast h
    have hB0 : Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔭)) = 0 := Nat.le_zero.1 (hA0 ▸ hs)
    rw [hB0, Nat.cast_zero]
    exact_mod_cast (zero_le : (0 : ℕ∞) ≤ 𝔭.height)
  ·
    obtain ⟨π, hπ𝔯, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    have hπ𝔭 : algebraMap R₀ B π ∈ 𝔭 := hπ𝔯
    have hπnzd : algebraMap R₀ B π ∈ nonZeroDivisors B := by
      rw [mem_nonZeroDivisors_iff_right]
      intro b hb
      apply hinj
      rw [map_zero]
      have hu : IsUnit (algebraMap B F (algebraMap R₀ B π)) :=
        IsLocalization.map_units F (⟨algebraMap R₀ B π, Algebra.mem_algebraMapSubmonoid_of_mem
          (⟨π, mem_nonZeroDivisors_of_ne_zero hπ0⟩ : nonZeroDivisors R₀)⟩ :
            Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀))
      have h := congrArg (algebraMap B F) hb
      rw [map_mul, map_zero] at h
      exact hu.mul_left_eq_zero.1 h
    have hnotmin : 𝔭 ∉ minimalPrimes B := fun hmin =>
      Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hmin) hπ𝔭 hπnzd
    have h𝔭1 : 1 ≤ 𝔭.height := ENat.one_le_iff_ne_zero.2 fun h => hnotmin (Ideal.height_eq_zero_iff.1 h)
    have hs1 : (Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔭)) : ℕ∞) ≤ 1 := by
      have h := (Nat.cast_le (α := ℕ∞)).2 hs
      exact h.trans (hsA'.trans_le hht)
    exact_mod_cast hs1.trans h𝔭1

end S_Algebra_IsUnramifiedAt_isRegularLocalRing_localization_of_ne_maximalIdeal
end P2MW
export P2MW.S_Algebra_IsUnramifiedAt_isRegularLocalRing_localization_of_ne_maximalIdeal (solution)
