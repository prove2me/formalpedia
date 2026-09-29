-- Prove2me | solution 1 for AlgebraicCurve.Place.algebraMap_coeff_neg_one_eq_localResidue_mul_differentialCoeff_D
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/cceed1da-bcd9-560a-b432-b591a3e78eab

import Mathlib
import Definitions.Def_AlgebraicCurve_LocalResidue
import Theorems.Thm_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_inv_eq_one
import Theorems.Thm_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_algebraMap_coeff_neg_one_eq_localResidue_mul_differentialCoeff_D
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ResFFProof

open HahnSeries

variable {K : Type*} [Field K]

theorem single_one_one_zpow (n : ℤ) : (single 1 (1 : K) : LaurentSeries K) ^ n = single n 1 := by
  have hpow : ∀ m : ℕ, (single 1 (1 : K) : LaurentSeries K) ^ m = single (m : ℤ) 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ih, HahnSeries.single_mul_single, one_mul]
      norm_cast
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · exact_mod_cast hpow m
  · rw [zpow_neg, zpow_natCast, hpow m]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [HahnSeries.single_mul_single, one_mul]
    simp

theorem mem_range_ofPowerSeries_iff (y : LaurentSeries K) :
    y ∈ (ofPowerSeries ℤ K).range ↔ ∀ j : ℤ, j < 0 → y.coeff j = 0 := by
  constructor
  · rintro ⟨p, rfl⟩ j hj
    rw [HahnSeries.ofPowerSeries_apply]
    apply HahnSeries.embDomain_notin_range
    rintro ⟨n, hn⟩
    simp at hn
    omega
  · intro hy
    refine ⟨PowerSeries.mk fun n => y.coeff n, ?_⟩
    ext j
    rcases lt_or_ge j 0 with hj | hj
    · rw [hy j hj, HahnSeries.ofPowerSeries_apply]
      apply HahnSeries.embDomain_notin_range
      rintro ⟨n, hn⟩
      simp at hn
      omega
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
      rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]

theorem exists_coeff_eq_zero_of_lt (x : LaurentSeries K) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j : ℤ, j < -(N : ℤ) → x.coeff j = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨1, le_rfl, fun j _ => rfl⟩
  refine ⟨(-x.order).toNat + 1, by omega, fun j hj => HahnSeries.coeff_eq_zero_of_lt_order ?_⟩
  have := Int.self_le_toNat (-x.order)
  push_cast at hj
  omega

theorem inv_mem_range_ofPowerSeries {p : PowerSeries K} (hp : PowerSeries.constantCoeff p ≠ 0) :
    ((ofPowerSeries ℤ K p : LaurentSeries K))⁻¹ ∈ (ofPowerSeries ℤ K).range := by
  refine ⟨p⁻¹, ?_⟩
  have hmul : p * p⁻¹ = 1 := PowerSeries.mul_inv_cancel p hp
  have hne : (ofPowerSeries ℤ K p : LaurentSeries K) ≠ 0 := by
    intro h0
    apply hp
    have : p = 0 := HahnSeries.ofPowerSeries_injective (by rw [h0, map_zero])
    rw [this, map_zero]
  refine (eq_inv_of_mul_eq_one_right ?_)
  rw [← map_mul, hmul, map_one]

theorem exists_eq_single_one_mul {p : PowerSeries K} (hp : PowerSeries.constantCoeff p = 0) :
    ∃ q : PowerSeries K, (ofPowerSeries ℤ K p : LaurentSeries K) = single 1 1 * ofPowerSeries ℤ K q := by
  obtain ⟨q, rfl⟩ : PowerSeries.X ∣ p := PowerSeries.X_dvd_iff.mpr (by simpa using hp)
  exact ⟨q, by rw [map_mul, HahnSeries.ofPowerSeries_X]⟩

end ResFFProof

namespace ResFFProof

open HahnSeries AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem zpow_mem_of_nonneg (v : Place K F) {x : F} (hx : x ∈ v.toValuationSubring) {m : ℤ} (hm : 0 ≤ m) :
    x ^ m ∈ v.toValuationSubring := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  rw [zpow_natCast]
  exact pow_mem hx k

theorem coe_unit_mul_coe_unit_inv (v : Place K F) (u : v.toValuationSubringˣ) :
    ((u : v.toValuationSubring) : F) * (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = 1 := by
  rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]

theorem ord_nonneg_of_mem (v : Place K F) {x : F} (hxO : x ∈ v.toValuationSubring) (hx : x ≠ 0) :
    0 ≤ v.ord x := by
  rw [← not_lt]
  intro hneg
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπne : (π : F) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  set n : ℤ := v.ord x with hn
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hx hπ
  rw [← hn] at hu

  obtain ⟨k, hk⟩ : ∃ k : ℕ, -n = k + 1 := ⟨(-n - 1).toNat, by omega⟩
  have hkey : (π : F) * ((π : F) ^ k * x * (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F)) = 1 := by
    have : x * (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = (π : F) ^ n := by
      rw [hu, mul_right_comm, coe_unit_mul_coe_unit_inv, one_mul]
    rw [mul_assoc, this, ← zpow_natCast, ← zpow_add₀ hπne, ← zpow_one_add₀ hπne,
      show (1 : ℤ) + (k + n) = 0 by omega, zpow_zero]
  apply hπ.not_isUnit
  let b : v.toValuationSubring := ⟨_, mul_mem (mul_mem (pow_mem π.2 k) hxO) (u⁻¹ : v.toValuationSubringˣ).val.2⟩
  have hb : π * b = 1 := Subtype.ext (by rw [MulMemClass.coe_mul, OneMemClass.coe_one]; exact hkey)
  exact ⟨⟨π, b, hb, (mul_comm b π).trans hb⟩, rfl⟩

theorem ord_pos_of_inv_not_mem (v : Place K F) {x : F} (hx : x ≠ 0) (hinv : x⁻¹ ∉ v.toValuationSubring) :
    1 ≤ v.ord x := by
  rw [← not_lt]
  intro hle
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  set n : ℤ := v.ord x with hn
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hx hπ
  rw [← hn] at hu
  apply hinv
  have : x⁻¹ = (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) * (π : F) ^ (-n) := by
    rw [hu, mul_inv, zpow_neg]
    congr 1
    refine inv_eq_of_mul_eq_one_right ?_
    exact coe_unit_mul_coe_unit_inv v u
  rw [this]
  exact mul_mem (u⁻¹ : v.toValuationSubringˣ).val.2 (zpow_mem_of_nonneg v π.2 (by omega))

theorem ord_eq_one_of_chart (v : Place K F)
    (Λ : F →+* LaurentSeries K)
    (hΛv : ∀ f : F, f ∈ v.toValuationSubring ↔ Λ f ∈ (ofPowerSeries ℤ K).range)
    {t₀ : F} (ht₀ : Λ t₀ = single 1 1) :
    t₀ ∈ v.toValuationSubring ∧ t₀ ≠ 0 ∧ v.ord t₀ = 1 := by
  have ht₀O : t₀ ∈ v.toValuationSubring := by
    rw [hΛv, ht₀, ← HahnSeries.ofPowerSeries_X]
    exact ⟨_, rfl⟩
  have ht₀ne : t₀ ≠ 0 := by
    intro h0
    have : (single 1 (1 : K) : LaurentSeries K) = 0 := by rw [← ht₀, h0, map_zero]
    exact one_ne_zero (HahnSeries.single_eq_zero_iff.mp this)
  have hΛt₀inv : Λ t₀⁻¹ = single (-1) 1 := by
    rw [map_inv₀, ht₀, ← single_one_one_zpow (-1 : ℤ), zpow_neg, zpow_one]

  have ht₀inv : t₀⁻¹ ∉ v.toValuationSubring := by
    rw [hΛv, hΛt₀inv, mem_range_ofPowerSeries_iff]
    intro h
    have := h (-1) (by norm_num)
    rw [HahnSeries.coeff_single_same] at this
    exact one_ne_zero this

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπne : (π : F) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  obtain ⟨p, hp⟩ : Λ (π : F) ∈ (ofPowerSeries ℤ K).range := (hΛv _).mp π.2
  have hp0 : PowerSeries.constantCoeff p = 0 := by
    by_contra hp0
    have hinvO : (π : F)⁻¹ ∈ v.toValuationSubring := by
      rw [hΛv, map_inv₀, ← hp]
      exact inv_mem_range_ofPowerSeries hp0
    apply hπ.not_isUnit
    let b : v.toValuationSubring := ⟨(π : F)⁻¹, hinvO⟩
    have hb : π * b = 1 := Subtype.ext (by rw [MulMemClass.coe_mul, OneMemClass.coe_one]; exact mul_inv_cancel₀ hπne)
    exact ⟨⟨π, b, hb, (mul_comm b π).trans hb⟩, rfl⟩
  obtain ⟨q, hq⟩ := exists_eq_single_one_mul hp0
  set a : F := (π : F) * t₀⁻¹ with ha_def
  have haO : a ∈ v.toValuationSubring := by
    rw [hΛv, ha_def, map_mul, hΛt₀inv, ← hp, hq, mul_comm (single 1 (1 : K) : LaurentSeries K), mul_assoc,
      HahnSeries.single_mul_single]
    refine ⟨q, ?_⟩
    simp
  have hπeq : (π : F) = t₀ * a := by rw [ha_def, mul_left_comm, mul_inv_cancel₀ ht₀ne, mul_one]
  have hane : a ≠ 0 := by
    intro h0; exact hπne (by rw [hπeq, h0, mul_zero])
  have h1 : v.ord (π : F) = v.ord t₀ + v.ord a := by rw [hπeq, v.ord_mul ht₀ne hane]
  rw [v.ord_coe_irreducible hπ] at h1
  have h2 := ord_nonneg_of_mem v haO hane
  have h3 := ord_pos_of_inv_not_mem v ht₀ne ht₀inv
  exact ⟨ht₀O, ht₀ne, by omega⟩

end ResFFProof

namespace ResFFProof

open HahnSeries AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem chart_algebraMap_mul_zpow (Λ : F →+* LaurentSeries K) (hΛC : ∀ c : K, Λ (algebraMap K F c) = C c)
    {t₀ : F} (ht₀ : Λ t₀ = single 1 1) (c : K) (j : ℤ) :
    Λ (algebraMap K F c * t₀ ^ j) = single j c := by
  rw [map_mul, hΛC, map_zpow₀, ht₀, single_one_one_zpow, HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add,
    mul_one]

theorem coeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries K) (i : ℤ) :
    (∑ j ∈ s, f j).coeff i = ∑ j ∈ s, (f j).coeff i := by
  change HahnSeries.coeff.linearMap (R := K) i (∑ j ∈ s, f j) = ∑ j ∈ s, HahnSeries.coeff.linearMap (R := K) i (f j)
  rw [map_sum]

theorem main [HasCanonicalLocalResidueKStar K F]
    (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (Λ : F →+* LaurentSeries K) (hΛC : ∀ c : K, Λ (algebraMap K F c) = C c)
    (hΛv : ∀ f : F, f ∈ v.toValuationSubring ↔ Λ f ∈ (ofPowerSeries ℤ K).range)
    {t₀ : F} (ht₀ : Λ t₀ = single 1 1) (h : F) :
    algebraMap K v.ResidueField ((Λ h).coeff (-1)) =
      v.localResidue (h * v.differentialCoeff (KaehlerDifferential.D K F t₀)) := by
  classical
  obtain ⟨ht₀O, ht₀ne, hord⟩ := ord_eq_one_of_chart v Λ hΛv ht₀
  set R := HasCanonicalLocalResidueKStar.dataKStar (K := K) (F := F) v with hR
  have hres : ∀ f : F, v.localResidue f = R.res f := fun f => rfl
  set δ : F := v.differentialCoeff (KaehlerDifferential.D K F t₀) with hδ
  have hδO : δ ∈ v.toValuationSubring := hint t₀ ht₀O

  have hrow : ∀ (j : ℤ), j < 0 → ∀ c : K,
      R.res (algebraMap K F c * t₀ ^ j * δ) = if j = -1 then algebraMap K v.ResidueField c else 0 := by
    intro j hj c
    rw [mul_assoc, ← Algebra.smul_def, LinearMap.map_smul]
    split_ifs with hj1
    · subst hj1
      rw [zpow_neg, zpow_one, mul_comm,
        Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_eq_one v hint R hord,
        Algebra.algebraMap_eq_smul_one]
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, j = -((n : ℤ) + 1) := ⟨(-j - 1).toNat, by omega⟩
      have hn1 : 1 ≤ n := by omega
      rw [hn, zpow_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, mul_comm,
        Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap
          v hsurj hint R hord hn1, smul_zero]

  obtain ⟨N, hN1, hN⟩ := exists_coeff_eq_zero_of_lt (Λ h)
  set P : F := ∑ j ∈ Finset.Ico (-(N : ℤ)) 0, algebraMap K F ((Λ h).coeff j) * t₀ ^ j with hP
  have hcoeffP : ∀ i : ℤ, (Λ P).coeff i = if i ∈ Finset.Ico (-(N : ℤ)) 0 then (Λ h).coeff i else 0 := by
    intro i
    rw [hP, map_sum, coeff_finset_sum]
    trans ∑ j ∈ Finset.Ico (-(N : ℤ)) 0, (if i = j then (Λ h).coeff j else 0)
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [chart_algebraMap_mul_zpow Λ hΛC ht₀ _ j, HahnSeries.coeff_single]
      split_ifs <;> rfl
    · exact Finset.sum_ite_eq _ _ _
  have h0O : h - P ∈ v.toValuationSubring := by
    rw [hΛv, mem_range_ofPowerSeries_iff]
    intro i hi
    have hsub : (Λ h - Λ P).coeff i = (Λ h).coeff i - (Λ P).coeff i := by
      change HahnSeries.coeff.linearMap (R := K) i (Λ h - Λ P) = _
      rw [map_sub]; rfl
    rw [map_sub, hsub, hcoeffP]
    split_ifs with hmem
    · exact sub_self _
    · rw [sub_zero]
      apply hN
      rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hmem
      omega

  have hsplit : h * δ = P * δ + (h - P) * δ := by ring
  rw [hres, hsplit, map_add, R.res_of_mem _ (mul_mem h0O hδO), add_zero, hP, Finset.sum_mul, map_sum,
    Finset.sum_congr rfl fun j hj => hrow j (Finset.mem_Ico.mp hj).2 _, Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_Ico.mpr ⟨by omega, by norm_num⟩)]

end ResFFProof

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    (v : AlgebraicCurve.Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (Λ : F →+* LaurentSeries K) (hΛC : ∀ c : K, Λ (algebraMap K F c) = HahnSeries.C c)
    (hΛv : ∀ f : F, f ∈ v.toValuationSubring ↔ Λ f ∈ (HahnSeries.ofPowerSeries ℤ K).range)
    {t₀ : F} (ht₀ : Λ t₀ = HahnSeries.single 1 1) (h : F) :
    algebraMap K v.ResidueField ((Λ h).coeff (-1)) =
      v.localResidue (h * v.differentialCoeff (KaehlerDifferential.D K F t₀)) :=
  ResFFProof.main v hsurj hint Λ hΛC hΛv ht₀ h

end S_AlgebraicCurve_Place_algebraMap_coeff_neg_one_eq_localResidue_mul_differentialCoeff_D
end P2MW
export P2MW.S_AlgebraicCurve_Place_algebraMap_coeff_neg_one_eq_localResidue_mul_differentialCoeff_D (solution)
