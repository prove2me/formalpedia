-- Prove2me | solution 1 for Algebra.exists_mem_comap_one_div_traceDual_mul_eq_mul_of_height_eq_one_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/11a99b64-187a-58e2-b32f-c660078a4a36

import Mathlib
import Theorems.Thm_Ideal_ramificationIdx_pow_not_dvd_differentIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_mem_comap_one_div_traceDual_mul_eq_mul_of_height_eq_one_of_charZero

set_option autoImplicit false
universe u
open IsLocalRing nonZeroDivisors Algebra Module

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace KA1Aux

theorem isSeparable_fractionRing_of_isSeparable
    (A B : Type u) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    (K' L' : Type u) [Field K'] [Field L'] [Algebra A K'] [IsFractionRing A K'] [Algebra B L'] [IsFractionRing B L']
    [Algebra K' L'] [Algebra A L'] [IsScalarTower A K' L'] [IsScalarTower A B L'] [Algebra.IsSeparable K' L'] :
    Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
  let e₁ : K' ≃ₐ[A] FractionRing A := (FractionRing.algEquiv A K').symm
  let e₂ : L' ≃ₐ[B] FractionRing B := (FractionRing.algEquiv B L').symm
  refine Algebra.IsSeparable.of_equiv_equiv e₁.toRingEquiv e₂.toRingEquiv ?_
  apply IsLocalization.ringHom_ext A⁰
  ext a
  simp only [RingHom.comp_apply]
  change algebraMap (FractionRing A) (FractionRing B) (e₁ (algebraMap A K' a)) = e₂ (algebraMap K' L' (algebraMap A K' a))
  rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply A B L', AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

theorem dimensionLEOne_of_ringKrullDim_le_one (R : Type*) [CommRing R] [IsDomain R]
    (h : ringKrullDim R ≤ 1) : Ring.DimensionLEOne R := by
  refine ⟨fun {p} hp hpp => ?_⟩
  by_contra hmax
  obtain ⟨m, hm, hpm⟩ := p.exists_le_maximal hpp.ne_top
  have hlt : p < m := lt_of_le_of_ne hpm (fun h' => hmax (h' ▸ hm))
  haveI := hm.isPrime
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hp)
  rw [Ideal.height_bot, zero_add] at h1
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hm2 : (2 : ℕ∞) ≤ m.height := by
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ p.height + 1 := by gcongr
      _ ≤ _ := h2
  have hm1 : m.height ≤ 1 := by
    have := (Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top).trans h
    have h1' : (1 : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) := rfl
    rw [h1'] at this
    exact WithBot.coe_le_coe.mp this
  have : (2 : ℕ∞) ≤ 1 := hm2.trans hm1
  exact absurd this (by norm_num)

theorem exists_mem_comap_one_div_traceDual_of_forall_exists_mul_mem
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Algebra.IsSeparable K L]
    (M : Submonoid A) (σ : L)
    (h : ∀ c ∈ Submodule.traceDual A K (1 : Submodule B L), ∃ m ∈ M, algebraMap A L m * σ * c ∈ (1 : Submodule B L)) :
    ∃ m ∈ M, ∃ s ∈ ((1 / Submodule.traceDual A K (1 : Submodule B L) : Submodule B L).comap (Algebra.linearMap B L)),
      algebraMap B L s = algebraMap A L m * σ := by
  classical

  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  haveI : IsIntegralClosure B A L :=
    ⟨IsFractionRing.injective B L, fun {x} =>
      ⟨fun hx => IsIntegrallyClosed.isIntegral_iff.mp hx.tower_top,
       fun ⟨y, hy⟩ => hy ▸ (Algebra.IsIntegral.isIntegral (R := A) y).algebraMap⟩⟩
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization_of_isSeparable A K L B
  let ι := Module.Free.ChooseBasisIndex A B
  let bB : Module.Basis ι A B := Module.Free.chooseBasis A B
  let bL : Module.Basis ι K L := bB.localizationLocalization K A⁰ L
  haveI : FiniteDimensional K L := Module.Finite.of_basis bL
  set C : Submodule B L := Submodule.traceDual A K (1 : Submodule B L) with hCdef
  have hspan : (1 : Submodule B L).restrictScalars A = Submodule.span A (Set.range bL) := by
    rw [Module.Basis.localizationLocalization_span]
    ext x
    simp only [Submodule.restrictScalars_mem, Submodule.mem_one, LinearMap.mem_range]
    rfl
  have hC : C.restrictScalars A = Submodule.span A (Set.range bL.traceDual) :=
    Submodule.traceDual_span_of_basis A (1 : Submodule B L) bL hspan
  have hCmem : ∀ c : L, c ∈ C ↔ c ∈ Submodule.span A (Set.range bL.traceDual) := fun c => by
    rw [← hC, Submodule.restrictScalars_mem]

  have h1C : (1 : L) ∈ C := by
    rw [hCdef, Submodule.mem_traceDual]
    intro a ha
    obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
    rw [Algebra.traceForm_apply, one_mul]
    have hint : IsIntegral A (algebraMap B L b) := (Algebra.IsIntegral.isIntegral (R := A) b).algebraMap
    exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace hint)

  have hci : ∀ i, (bL.traceDual i : L) ∈ C := fun i => (hCmem _).mpr (Submodule.subset_span ⟨i, rfl⟩)
  choose m hm hmB using fun i => h _ (hci i)
  obtain ⟨m₀, hm₀, hm₀B⟩ := h 1 h1C
  refine ⟨m₀ * ∏ i, m i, M.mul_mem hm₀ (M.prod_mem fun i _ => hm i), ?_⟩
  obtain ⟨s, hs⟩ := Submodule.mem_one.mp hm₀B

  refine ⟨(algebraMap A B (∏ i, m i)) * s, ?_, ?_⟩
  ·
    rw [Submodule.mem_comap, Algebra.linearMap_apply, Submodule.mem_div_iff_forall_mul_mem]
    intro c hc
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp ((hCmem c).mp hc)
    rw [Finset.mul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [mul_smul_comm]
    refine Submodule.smul_of_tower_mem _ (a i) ?_

    obtain ⟨bi, hbi⟩ := Submodule.mem_one.mp (hmB i)
    obtain ⟨r, hr⟩ : m i ∣ ∏ j, m j := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    refine Submodule.mem_one.mpr ⟨algebraMap A B (m₀ * r) * bi, ?_⟩
    show algebraMap B L (algebraMap A B (m₀ * r) * bi) = algebraMap B L (algebraMap A B (∏ j, m j) * s) * (bL.traceDual i)
    simp only [map_mul, hbi, hs, ← IsScalarTower.algebraMap_apply A B L, hr, mul_one]
    ring
  · rw [map_mul, hs, ← IsScalarTower.algebraMap_apply A B L, map_mul, map_prod]
    simp only [mul_one]
    ring

theorem exists_mul_mem_comap_one_div_traceDual
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (𝔭 : Ideal R) [𝔭.IsPrime]
    (R𝔭 S𝔭 : Type u) [CommRing R𝔭] [CommRing S𝔭] [Algebra R R𝔭] [IsLocalization.AtPrime R𝔭 𝔭]
    [Algebra S S𝔭] [IsLocalization (Algebra.algebraMapSubmonoid S 𝔭.primeCompl) S𝔭]
    [Algebra R𝔭 S𝔭] [Algebra R𝔭 K] [IsScalarTower R R𝔭 K]
    [Algebra S𝔭 F] [IsScalarTower S S𝔭 F] [IsFractionRing S𝔭 F] [Algebra R𝔭 F] [IsScalarTower R𝔭 K F] [IsScalarTower R𝔭 S𝔭 F]
    (σ : S𝔭) (hσ : algebraMap S𝔭 F σ ∈ (1 / Submodule.traceDual R𝔭 K (1 : Submodule S𝔭 F) : Submodule S𝔭 F)) :
    ∃ s : S, s ∈ ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F)) ∧
      ∃ m ∈ Algebra.algebraMapSubmonoid S 𝔭.primeCompl, algebraMap S S𝔭 s = algebraMap S S𝔭 m * σ := by
  classical
  have hinjRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hRF : ∀ r : R, algebraMap R F r = algebraMap K F (algebraMap R K r) := fun r => IsScalarTower.algebraMap_apply R K F r
  have hRSF : ∀ r : R, algebraMap R F r = algebraMap S F (algebraMap R S r) := fun r => IsScalarTower.algebraMap_apply R S F r
  have hSF : ∀ s : S, algebraMap S F s = algebraMap S𝔭 F (algebraMap S S𝔭 s) := fun s => IsScalarTower.algebraMap_apply S S𝔭 F s

  have hCC : ∀ c ∈ Submodule.traceDual R K (1 : Submodule S F), c ∈ Submodule.traceDual R𝔭 K (1 : Submodule S𝔭 F) := by
    intro c hc
    rw [Submodule.mem_traceDual] at hc ⊢
    intro a ha
    obtain ⟨β, rfl⟩ := Submodule.mem_one.mp ha
    obtain ⟨⟨b, ⟨_, m, hm, rfl⟩⟩, hβ⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid S 𝔭.primeCompl) β

    have hm0 : algebraMap R K m ≠ 0 := fun h => hm (by
      have : m = 0 := hinjRK (by rw [h, map_zero]); rw [this]; exact 𝔭.zero_mem)
    have hβF : algebraMap S𝔭 F β = (algebraMap R K m)⁻¹ • algebraMap S F b := by
      have h1 : algebraMap S𝔭 F β * algebraMap K F (algebraMap R K m) = algebraMap S F b := by
        rw [← hRF, hRSF, hSF, hSF, ← map_mul, hβ]
      rw [Algebra.smul_def, map_inv₀, eq_inv_mul_iff_mul_eq₀ ((map_ne_zero_iff _ (algebraMap K F).injective).mpr hm0),
        mul_comm, h1]
    obtain ⟨r, hr⟩ := hc (algebraMap S F b) (Submodule.mem_one.mpr ⟨b, rfl⟩)
    rw [hβF, Algebra.traceForm_apply, mul_smul_comm, map_smul, ← Algebra.traceForm_apply, ← hr]
    refine ⟨IsLocalization.mk' R𝔭 r ⟨m, hm⟩, ?_⟩
    have h2 : algebraMap R𝔭 K (IsLocalization.mk' R𝔭 r ⟨m, hm⟩) * algebraMap R K m = algebraMap R K r := by
      rw [IsScalarTower.algebraMap_apply R R𝔭 K m, ← map_mul, IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply]
    rw [smul_eq_mul, eq_inv_mul_iff_mul_eq₀ hm0, mul_comm]
    exact h2

  have hmain := exists_mem_comap_one_div_traceDual_of_forall_exists_mul_mem R K S F 𝔭.primeCompl (algebraMap S𝔭 F σ) (by
    intro c hc
    have hσc : algebraMap S𝔭 F σ * c ∈ (1 : Submodule S𝔭 F) :=
      (Submodule.mem_div_iff_forall_mul_mem.mp hσ) c (hCC c hc)
    obtain ⟨β, hβ⟩ := Submodule.mem_one.mp hσc
    obtain ⟨⟨b, ⟨_, m, hm, rfl⟩⟩, hβm⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid S 𝔭.primeCompl) β
    refine ⟨m, hm, Submodule.mem_one.mpr ⟨b, ?_⟩⟩
    rw [mul_assoc, ← hβ, hRSF, hSF, hSF, ← map_mul, mul_comm, hβm])
  obtain ⟨m, hm, s, hs, hsσ⟩ := hmain
  refine ⟨s, hs, algebraMap R S m, ⟨m, hm, rfl⟩, ?_⟩
  apply IsFractionRing.injective S𝔭 F
  rw [← hSF, hsσ, map_mul, ← hSF, ← hRSF]

end KA1Aux

open KA1Aux in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (t : R) (ht : (Ideal.span ({t} : Set R)).IsPrime) [CharZero (R ⧸ Ideal.span ({t} : Set R))]
    (𝔔 : Ideal S) [𝔔.IsPrime] (h𝔔 : 𝔔.height = 1) (ht𝔔 : algebraMap R S t ∈ 𝔔) :
    ∃ s ∈ ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F)), ∃ u ∉ 𝔔, ∃ z ∈ 𝔔, u * algebraMap R S t = s * z := by
  classical

  by_cases ht0 : t = 0
  · refine ⟨0, Submodule.zero_mem _, 1, fun h => (Ideal.IsPrime.ne_top ‹𝔔.IsPrime›) ((Ideal.eq_top_iff_one _).mpr h),
      0, 𝔔.zero_mem, by simp [ht0]⟩
  set 𝔭 : Ideal R := Ideal.span ({t} : Set R) with h𝔭def
  haveI h𝔭p : 𝔭.IsPrime := ht
  have ht𝔭 : t ∈ 𝔭 := Ideal.mem_span_singleton_self t
  have h𝔭0 : 𝔭 ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact ht0
  haveI : FaithfulSMul R S := inferInstance
  have hinjRS : Function.Injective (algebraMap R S) := FaithfulSMul.algebraMap_injective R S
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S

  have h𝔭1 : 𝔭.height = 1 := by
    apply le_antisymm
    · haveI : 𝔭.IsPrincipal := ⟨⟨t, rfl⟩⟩
      exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes 𝔭 𝔭 (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl)
    · have h := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr h𝔭0)
      rwa [Ideal.height_bot, zero_add] at h
  haveI : Algebra.HasGoingDown R S := inferInstance
  haveI h𝔔𝔭 : 𝔔.LiesOver 𝔭 := by
    constructor
    by_contra hne
    have hle : 𝔭 ≤ 𝔔.under R := by
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact ht𝔔
    have hlt : 𝔭 < 𝔔.under R := lt_of_le_of_ne hle hne
    obtain ⟨Q', hQ'lt, hQ'p, hQ'over⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := 𝔭) (q := 𝔔.under R) 𝔔 hlt
    have hQ'0 : (⊥ : Ideal S) < Q' := by
      rw [bot_lt_iff_ne_bot]
      intro h
      have : algebraMap R S t ∈ Q' := by
        have : t ∈ Q'.under R := by rw [← hQ'over.over]; exact ht𝔭
        exact this
      rw [h, Ideal.mem_bot, map_eq_zero_iff _ hinjRS] at this
      exact ht0 this
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hQ'0
    rw [Ideal.height_bot, zero_add] at h1
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hQ'lt
    rw [h𝔔] at h2
    have : (2 : ℕ∞) ≤ 1 := by
      calc (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ Q'.height + 1 := by gcongr
        _ ≤ 1 := h2
    exact absurd this (by norm_num)
  have h𝔔under : 𝔔.under R = 𝔭 := h𝔔𝔭.over.symm

  set M : Submonoid S := Algebra.algebraMapSubmonoid S 𝔭.primeCompl with hM
  let R𝔭 := Localization.AtPrime 𝔭
  let S𝔭 := Localization M
  have hMle : M ≤ S⁰ := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinjRS).mpr (fun h => hr (h.symm ▸ 𝔭.zero_mem)))
  haveI : IsDomain S𝔭 := IsLocalization.isDomain_localization hMle
  letI algRK : Algebra R𝔭 K := IsLocalization.localizationAlgebraOfSubmonoidLe R𝔭 K 𝔭.primeCompl R⁰ 𝔭.primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower R R𝔭 K := IsLocalization.localization_isScalarTower_of_submonoid_le R𝔭 K 𝔭.primeCompl R⁰ 𝔭.primeCompl_le_nonZeroDivisors
  haveI : IsFractionRing R𝔭 K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl R𝔭 K
  letI algSF : Algebra S𝔭 F := IsLocalization.localizationAlgebraOfSubmonoidLe S𝔭 F M S⁰ hMle
  haveI : IsScalarTower S S𝔭 F := IsLocalization.localization_isScalarTower_of_submonoid_le S𝔭 F M S⁰ hMle
  haveI : IsFractionRing S𝔭 F := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S𝔭 F
  letI algRF : Algebra R𝔭 F := ((algebraMap K F).comp (algebraMap R𝔭 K)).toAlgebra
  haveI : IsScalarTower R𝔭 K F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R R𝔭 F := IsScalarTower.of_algebraMap_eq (fun r => by
    show _ = algebraMap K F (algebraMap R𝔭 K (algebraMap R R𝔭 r))
    rw [← IsScalarTower.algebraMap_apply R R𝔭 K, ← IsScalarTower.algebraMap_apply R K F])
  haveI : IsScalarTower R𝔭 S𝔭 F := IsScalarTower.of_algebraMap_eq' (by
    apply IsLocalization.ringHom_ext 𝔭.primeCompl
    ext r
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R R𝔭 F, ← IsScalarTower.algebraMap_apply R R𝔭 S𝔭,
      IsScalarTower.algebraMap_apply R S S𝔭 r, ← IsScalarTower.algebraMap_apply S S𝔭 F,
      ← IsScalarTower.algebraMap_apply R S F])
  haveI : IsNoetherianRing R𝔭 := IsLocalization.isNoetherianRing 𝔭.primeCompl R𝔭 inferInstance
  haveI : IsNoetherianRing S𝔭 := IsLocalization.isNoetherianRing M S𝔭 inferInstance
  haveI : IsIntegrallyClosed R𝔭 := isIntegrallyClosed_of_isLocalization (R := R) (S := R𝔭) 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors
  haveI : IsIntegrallyClosed S𝔭 := isIntegrallyClosed_of_isLocalization (R := S) (S := S𝔭) M hMle
  have hinj𝔭 : Function.Injective (algebraMap R𝔭 S𝔭) := localizationAlgebra_injective (M := 𝔭.primeCompl) R𝔭 S𝔭 hinjRS
  haveI : FaithfulSMul R𝔭 S𝔭 := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj𝔭
  haveI : Module.IsTorsionFree R𝔭 S𝔭 := Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  haveI : Algebra.IsIntegral R𝔭 S𝔭 := Algebra.IsIntegral.of_finite _ _

  have hdimR : ringKrullDim R𝔭 = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 R𝔭, h𝔭1]; rfl
  haveI : Ring.DimensionLEOne R𝔭 := dimensionLEOne_of_ringKrullDim_le_one R𝔭 hdimR.le
  haveI : IsDedekindDomain R𝔭 :=
    { (inferInstance : IsNoetherianRing R𝔭), (inferInstance : Ring.DimensionLEOne R𝔭),
      (inferInstance : IsIntegrallyClosed R𝔭) with }
  haveI : Ring.DimensionLEOne S𝔭 := Ring.DimensionLEOne.of_isIntegral (R := R𝔭) S𝔭
  haveI : IsDedekindDomain S𝔭 :=
    { (inferInstance : IsNoetherianRing S𝔭), (inferInstance : Ring.DimensionLEOne S𝔭),
      (inferInstance : IsIntegrallyClosed S𝔭) with }

  have hdisj : Disjoint (M : Set S) (𝔔 : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hq
    apply hr
    have : r ∈ 𝔔.under R := hq
    rwa [h𝔔under] at this
  set P : Ideal S𝔭 := 𝔔.map (algebraMap S S𝔭) with hPdef
  haveI hPp : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M S𝔭 𝔔 inferInstance hdisj
  have hPunder : P.comap (algebraMap S S𝔭) = 𝔔 := IsLocalization.under_map_of_isPrime_disjoint M S𝔭 inferInstance hdisj
  have ht' : algebraMap S S𝔭 (algebraMap R S t) ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective S𝔭 hMle)).mpr ((map_ne_zero_iff _ hinjRS).mpr ht0)
  have htP : algebraMap S S𝔭 (algebraMap R S t) ∈ P := Ideal.mem_map_of_mem _ ht𝔔
  have hP0 : P ≠ ⊥ := fun h => ht' (by rw [h, Ideal.mem_bot] at htP; exact htP)
  haveI hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal hPp hP0

  have hnf : ¬ IsField R𝔭 := IsLocalization.AtPrime.not_isField R h𝔭0 R𝔭
  have hp0 : maximalIdeal R𝔭 ≠ ⊥ := fun h => hnf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
  have htm : algebraMap R R𝔭 t ∈ maximalIdeal R𝔭 := (IsLocalization.AtPrime.to_map_mem_maximal_iff R𝔭 𝔭 t).mpr ht𝔭
  haveI hPlies : P.LiesOver (maximalIdeal R𝔭) := by
    constructor
    haveI : (P.under R𝔭).IsPrime := inferInstance
    have hne : P.under R𝔭 ≠ ⊥ := by
      intro h
      have : algebraMap R𝔭 S𝔭 (algebraMap R R𝔭 t) ∈ P := by
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S S𝔭]; exact htP
      have : algebraMap R R𝔭 t ∈ P.under R𝔭 := this
      rw [h, Ideal.mem_bot] at this
      exact ht0 ((map_eq_zero_iff _ (IsLocalization.injective R𝔭 𝔭.primeCompl_le_nonZeroDivisors)).mp this)
    exact (IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne)).symm

  letI := Ideal.Quotient.field (maximalIdeal R𝔭)
  have hcm : (maximalIdeal R𝔭).comap (algebraMap R R𝔭) = 𝔭 := IsLocalization.AtPrime.under_maximalIdeal R𝔭 𝔭
  haveI : CharZero (R𝔭 ⧸ maximalIdeal R𝔭) := by
    refine charZero_of_injective_ringHom (f := Ideal.quotientMap (maximalIdeal R𝔭) (algebraMap R R𝔭) hcm.ge) ?_
    exact Ideal.quotientMap_injective' hcm.le
  haveI : Algebra.IsSeparable (R𝔭 ⧸ maximalIdeal R𝔭) (S𝔭 ⧸ P) := by
    haveI : Algebra.IsIntegral (R𝔭 ⧸ maximalIdeal R𝔭) (S𝔭 ⧸ P) := Algebra.IsIntegral.of_finite _ _
    exact ⟨fun x => PerfectField.separable_of_irreducible (minpoly.irreducible (Algebra.IsIntegral.isIntegral x))⟩
  have hsepFF := isSeparable_fractionRing_of_isSeparable R𝔭 S𝔭 K F
  haveI := hsepFF
  set e := Ideal.ramificationIdx' (maximalIdeal R𝔭) P with hedef
  have he0 : e ≠ 0 := Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
  have he : ((e : ℕ) : R𝔭 ⧸ maximalIdeal R𝔭) ≠ 0 := Nat.cast_ne_zero.mpr he0
  have hndvd := Ideal.ramificationIdx_pow_not_dvd_differentIdeal R𝔭 hp0 P he
  obtain ⟨σ, hσD, hσP⟩ : ∃ σ ∈ differentIdeal R𝔭 S𝔭, σ ∉ P ^ e := by
    rw [Ideal.dvd_iff_le, SetLike.not_le_iff_exists] at hndvd
    exact hndvd
  have htPe : algebraMap S S𝔭 (algebraMap R S t) ∈ P ^ e := by
    have : algebraMap R𝔭 S𝔭 (algebraMap R R𝔭 t) ∈ P ^ e :=
      Ideal.le_pow_ramificationIdx (Ideal.mem_map_of_mem _ htm)
    rwa [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S S𝔭] at this

  haveI : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) F := IsIntegralClosure.isLocalization R K F S
  haveI : FiniteDimensional K F := Module.Finite.of_isLocalization R S R⁰
  have hσ1 : algebraMap S𝔭 F σ ∈ (1 / Submodule.traceDual R𝔭 K (1 : Submodule S𝔭 F) : Submodule S𝔭 F) := by
    rw [← coeSubmodule_differentIdeal R𝔭 K]
    exact ⟨σ, hσD, rfl⟩
  obtain ⟨s, hs𝔇, m, hmM, hsσ⟩ := exists_mul_mem_comap_one_div_traceDual R K S F 𝔭 R𝔭 S𝔭 σ hσ1

  have hmunit : IsUnit (algebraMap S S𝔭 m) := IsLocalization.map_units S𝔭 ⟨m, hmM⟩
  have hsPe : algebraMap S S𝔭 s ∉ P ^ e := by
    intro h
    apply hσP
    obtain ⟨u, hu⟩ := hmunit
    have : σ = ↑u⁻¹ * algebraMap S S𝔭 s := by rw [hsσ, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ h

  have hs0 : algebraMap S S𝔭 s ≠ 0 := fun h => hsPe (by rw [h]; exact Ideal.zero_mem _)
  have hsI0 : Ideal.span {algebraMap S S𝔭 s} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hs0
  obtain ⟨Q, hPQ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hsI0 P
  set a := Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {algebraMap S S𝔭 s})) with hadef
  have hae : a < e := by
    by_contra h
    apply hsPe
    have : Ideal.span {algebraMap S S𝔭 s} ≤ P ^ e :=
      hfac.le.trans ((Ideal.mul_le_left).trans (Ideal.pow_le_pow_right (not_lt.mp h)))
    exact this (Ideal.mem_span_singleton_self _)

  obtain ⟨u', hu'Q, hu'P⟩ : ∃ u' ∈ Q, u' ∉ P := by
    by_contra h
    push Not at h
    have : Q ≤ P := h
    have : P ⊔ Q = P := sup_eq_left.mpr this
    exact hPmax.ne_top (this ▸ hPQ)

  have hmem : u' * algebraMap S S𝔭 (algebraMap R S t) ∈ Ideal.span {algebraMap S S𝔭 s} * P := by
    have h1 : algebraMap S S𝔭 (algebraMap R S t) ∈ P ^ a * P := by
      rw [← pow_succ]; exact Ideal.pow_le_pow_right (Nat.succ_le_of_lt hae) htPe
    have h2 : u' * algebraMap S S𝔭 (algebraMap R S t) ∈ Q * (P ^ a * P) := Ideal.mul_mem_mul hu'Q h1
    rw [hfac]
    have : Q * (P ^ a * P) = P ^ a * Q * P := by ring
    rwa [this] at h2
  obtain ⟨z', hz'P, hz'⟩ := Ideal.mem_span_singleton_mul.mp hmem

  obtain ⟨⟨u₁, mu⟩, hu₁⟩ := IsLocalization.mk'_surjective M u'
  obtain ⟨⟨z₁, mz⟩, hz₁⟩ := IsLocalization.mk'_surjective M z'
  simp only at hu₁ hz₁
  refine ⟨s, hs𝔇, (mz : S) * u₁, ?_, (mu : S) * z₁, ?_, ?_⟩
  ·
    intro h
    rcases (Ideal.IsPrime.mem_or_mem inferInstance h) with h1 | h1
    · exact (Set.disjoint_left.mp hdisj) mz.2 h1
    · apply hu'P
      rw [← hu₁, IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h1)
  ·
    apply Ideal.mul_mem_left
    rw [← hPunder, Ideal.mem_comap]
    have : algebraMap S S𝔭 z₁ = z' * algebraMap S S𝔭 (mz : S) := by
      rw [← hz₁]; exact (IsLocalization.mk'_spec S𝔭 z₁ mz).symm
    rw [this]
    exact Ideal.mul_mem_right _ _ hz'P
  ·
    have key : IsLocalization.mk' S𝔭 (algebraMap R S t * u₁) mu = IsLocalization.mk' S𝔭 (s * z₁) mz := by
      rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, ← IsLocalization.mul_mk'_eq_mk'_of_mul, hu₁, hz₁, hz', mul_comm]
    rw [IsLocalization.mk'_eq_iff_eq] at key
    have key' := IsLocalization.injective S𝔭 hMle key
    linear_combination key'

end S_Algebra_exists_mem_comap_one_div_traceDual_mul_eq_mul_of_height_eq_one_of_charZero
end P2MW
export P2MW.S_Algebra_exists_mem_comap_one_div_traceDual_mul_eq_mul_of_height_eq_one_of_charZero (solution)
