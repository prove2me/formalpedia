-- Prove2me | solution 1 for ArtinPrimitiveRoots.type_ii_progression
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T14:41:24.973988+00:00
-- url     : https://prove2.me/submissions/4a6716cd-f9df-4a4c-8e4f-2a81a21e722a

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_rough_factor_coefficient_bound
import Theorems.Thm_ArtinPrimitiveRoots_marked_type_ii_of_coefficient_bound
import Theorems.Thm_ArtinPrimitiveRoots_mertens_product
import Theorems.Thm_ArtinPrimitiveRoots_mertens_prime_reciprocals

namespace ArtinPrimitiveRoots.TypeIIProg

open Real Filter Topology MeasureTheory

/-! ## Characters -/

lemma char_indicator (M : ℕ) (hM : 0 < M) (u : ℤ) (hu : IsCoprime u M) (m n : ℕ) :
    (if ((m * n : ℕ) : ℤ) ≡ u [ZMOD M] then (1 : ℂ) else 0) =
      ∑ l : DirichletCharacter ℂ M,
        ((M.totient : ℂ)⁻¹ * l ((u : ZMod M))⁻¹) * (l (m : ZMod M) * l (n : ZMod M)) := by
  have : NeZero M := ⟨hM.ne'⟩
  have hunit : IsUnit ((u : ZMod M)) := by
    have := (ZMod.unitOfIsCoprime u hu).isUnit
    rwa [ZMod.coe_unitOfIsCoprime] at this
  have hsum := DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) hunit ((m * n : ℕ) : ZMod M)
  have htot : (M.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hM).ne'
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have h2 : ∑ l : DirichletCharacter ℂ M, l ((u : ZMod M))⁻¹ * (l (m : ZMod M) * l (n : ZMod M)) =
      ∑ l : DirichletCharacter ℂ M, l ((u : ZMod M))⁻¹ * l ((m * n : ℕ) : ZMod M) := by
    apply Finset.sum_congr rfl; intro l _; rw [Nat.cast_mul, map_mul]
  rw [h2, hsum]
  have hiff : ((u : ZMod M) = ((m * n : ℕ) : ZMod M)) ↔ ((m * n : ℕ) : ℤ) ≡ u [ZMOD M] := by
    rw [← ZMod.intCast_eq_intCast_iff, Int.cast_natCast]; exact eq_comm
  by_cases h : ((m * n : ℕ) : ℤ) ≡ u [ZMOD M]
  · rw [if_pos h, if_pos (hiff.mpr h), inv_mul_cancel₀ htot]
  · rw [if_neg h, if_neg (fun e => h (hiff.mp e)), mul_zero]

lemma changeLevel_mul_apply {M k : ℕ} (l : DirichletCharacter ℂ M) (χ : DirichletCharacter ℂ k)
    (m : ℕ) :
    (DirichletCharacter.changeLevel (dvd_mul_right M k) l *
      DirichletCharacter.changeLevel (dvd_mul_left k M) χ) (m : ZMod (M * k)) =
      l (m : ZMod M) * χ (m : ZMod k) := by
  rw [MulChar.coeToFun_mul, Pi.mul_apply]
  by_cases hcop : Nat.Coprime m (M * k)
  · have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd l (dvd_mul_right M k)
      (ZMod.unitOfCoprime m hcop)
    have h2 := DirichletCharacter.changeLevel_eq_cast_of_dvd χ (dvd_mul_left k M)
      (ZMod.unitOfCoprime m hcop)
    simp only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast (dvd_mul_right M k),
      ZMod.cast_natCast (dvd_mul_left k M)] at h1 h2
    rw [h1, h2]
  · have hnu : ¬ IsUnit ((m : ZMod (M * k))) := by rwa [ZMod.isUnit_iff_coprime]
    rw [MulChar.map_nonunit _ hnu, MulChar.map_nonunit _ hnu, zero_mul]
    rcases (not_and_or.mp (fun h : Nat.Coprime m M ∧ Nat.Coprime m k =>
      hcop (Nat.Coprime.mul_right h.1 h.2))) with h | h
    · rw [MulChar.map_nonunit l (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]
    · rw [MulChar.map_nonunit χ (by rwa [ZMod.isUnit_iff_coprime]), mul_zero]

/-! ## The invariant function `F` -/

lemma groupPrimes_prime (x : ℝ) {K : ℕ} (a : Fin K → ℝ) :
    ∀ p ∈ groupPrimes x a, p.Prime := by
  intro p hp
  simp only [groupPrimes, primeGroup, Finset.mem_biUnion, Finset.mem_filter] at hp
  obtain ⟨i, -, -, h, -⟩ := hp
  exact h

lemma groupPart_mul_prime (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) (hh : 0 < h) (p : ℕ)
    (hp : p ∈ groupPrimes x a) : groupPart x a (p * h) = p * groupPart x a h := by
  have hpp := groupPrimes_prime x a p hp
  unfold groupPart
  rw [Nat.factorization_mul hpp.ne_zero hh.ne']
  simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single_of_mem p hp]
  · rw [hpp.factorization_self, pow_one]
  · intro q _ hqp
    rw [hpp.factorization, Finsupp.single_apply, if_neg (Ne.symm hqp), pow_zero]

lemma predecessorIndicator_mul (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (c h : ℕ) (hh : 0 < h) (p : ℕ)
    (hp : p ∈ groupPrimes x a) : predecessorIndicator x a c (p * h) = predecessorIndicator x a c h := by
  have hpp := groupPrimes_prime x a p hp
  have : p * h / groupPart x a (p * h) = h / groupPart x a h := by
    rw [groupPart_mul_prime x a h hh p hp, Nat.mul_div_mul_left _ _ hpp.pos]
  unfold predecessorIndicator
  rw [this]

lemma predecessorIndicator_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (c h : ℕ) :
    0 ≤ predecessorIndicator x a c h := by
  unfold predecessorIndicator; split_ifs <;> norm_num

lemma predecessorIndicator_le_one (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (c h : ℕ) :
    predecessorIndicator x a c h ≤ 1 := by
  unfold predecessorIndicator; split_ifs <;> norm_num

/-! ## The mark is bounded -/

lemma groupReciprocalSum_nonneg (x a : ℝ) : 0 ≤ groupReciprocalSum x a := by
  unfold groupReciprocalSum
  apply Finset.sum_nonneg
  intro p _
  positivity

lemma mark_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : 0 ≤ mark (1 / 2) x a h := by
  unfold mark
  apply mul_nonneg (zpow_nonneg (by norm_num) _)
  apply Finset.prod_nonneg
  intro i _
  exact div_nonneg (Nat.cast_nonneg _) (groupReciprocalSum_nonneg _ _)

lemma two_mul_le_two_pow (n : ℕ) : 2 * n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · rw [pow_succ]; omega

lemma mark_le (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ)
    (hV : ∀ i, 1 / 2 ≤ groupReciprocalSum x (a i)) : mark (1 / 2) x a h ≤ 2 ^ K := by
  unfold mark markOmega
  set ω : Fin K → ℕ := fun i => groupOmega x (a i) h with hω
  have hnat : 2 ^ K * ∏ i, ω i ≤ 2 ^ (∑ i, ω i) := by
    have h1 : ∏ i, (2 * ω i) ≤ ∏ i, 2 ^ ω i :=
      Finset.prod_le_prod' (fun i _ => two_mul_le_two_pow (ω i))
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] at h1
    simpa using h1
  have hreal : (2 : ℝ) ^ K * ∏ i, (ω i : ℝ) ≤ 2 ^ (∑ i, ω i) := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this
    exact this
  have hz : ((1 : ℝ) / 2) ^ ((∑ i, ω i : ℕ) - (K : ℤ)) = 2 ^ K / 2 ^ (∑ i, ω i) := by
    rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, one_div_pow, one_div_pow]
    field_simp
  have hprod : ∏ i, (ω i : ℝ) / groupReciprocalSum x (a i) ≤ ∏ i, (ω i : ℝ) * 2 := by
    apply Finset.prod_le_prod
    · intro i _; exact div_nonneg (Nat.cast_nonneg _) (groupReciprocalSum_nonneg _ _)
    · intro i _
      rw [div_le_iff₀ (by linarith [hV i])]
      have := hV i
      have h0 : (0 : ℝ) ≤ ω i := Nat.cast_nonneg _
      nlinarith
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  rw [hz]
  have hpos : (0 : ℝ) < 2 ^ (∑ i, ω i) := by positivity
  calc (2 : ℝ) ^ K / 2 ^ (∑ i, ω i) * ∏ i, (ω i : ℝ) / groupReciprocalSum x (a i)
      ≤ 2 ^ K / 2 ^ (∑ i, ω i) * ((∏ i, (ω i : ℝ)) * 2 ^ K) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (2 ^ K * ∏ i, (ω i : ℝ)) / 2 ^ (∑ i, ω i) * 2 ^ K := by ring
    _ ≤ 1 * 2 ^ K := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [div_le_one hpos]; exact hreal
    _ = 2 ^ K := one_mul _

lemma eventually_groupReciprocalSum (a : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, 1 / 2 ≤ groupReciprocalSum x a := by
  have hm := mertens_prime_reciprocals 1 2 one_pos one_lt_two
  have hlog : (1 / 2 : ℝ) < log (2 / 1) := by
    rw [div_one]; have := Real.log_two_gt_d9; linarith
  have h1 := hm.eventually (eventually_gt_nhds hlog)
  have hX : Tendsto (fun x : ℝ => exp (log x ^ a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop)
  filter_upwards [hX.eventually h1] with x hx
  refine le_trans hx.le ?_
  unfold groupReciprocalSum primeGroup
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    refine ⟨?_, hp.2.1, ?_⟩
    · have : exp (log x ^ a) ^ (2 : ℝ) = exp (2 * log x ^ a) := by
        rw [← Real.exp_mul, mul_comm]
      rw [← this]; exact hp.1
    · have := hp.2.2
      rw [Real.rpow_one] at this
      exact this.le
  · intro p _ _
    positivity

/-- The invariant weight `F(h) 𝒲(h)`. -/
noncomputable def G (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (c h : ℕ) : ℂ :=
  (predecessorIndicator x a c h : ℂ) * (mark (1 / 2) x a h : ℂ)

lemma norm_G_le (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (c h : ℕ)
    (hV : ∀ i, 1 / 2 ≤ groupReciprocalSum x (a i)) : ‖G x a c h‖ ≤ 2 ^ K := by
  unfold G
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (predecessorIndicator_nonneg _ _ _ _), abs_of_nonneg (mark_nonneg _ _ _)]
  calc _ ≤ 1 * 2 ^ K := mul_le_mul (predecessorIndicator_le_one _ _ _ _) (mark_le x a h hV)
        (mark_nonneg _ _ _) zero_le_one
    _ = _ := one_mul _

/-! ## A bound for the rough-number density on `[γ, 1]` -/

lemma roughDensityTerm_abs_le (γ w : ℝ) (hγ : 0 < γ) (hγw : γ ≤ w) (hw : w ≤ 1) (j : ℕ) :
    |roughDensityTerm γ w j| ≤ (1 / γ) ^ j / (j.factorial : ℝ) := by
  rcases j with _ | _ | j
  · simp [roughDensityTerm]
  · show |1 / w| ≤ (1 / γ) ^ 1 / ((Nat.factorial 1 : ℕ) : ℝ)
    rw [abs_of_pos (by have := hγ.trans_le hγw; positivity)]
    simpa using one_div_le_one_div_of_le hγ hγw
  · show |(1 / ((j + 2).factorial : ℝ)) *
      ∫ t in {t : Fin (j + 1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ},
        (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹| ≤ (1 / γ) ^ (j + 2) / ((j + 2).factorial : ℝ)
    set s := {t : Fin (j + 1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ} with hs
    have hsub : s ⊆ Set.Icc (0 : Fin (j + 1) → ℝ) 1 := by
      intro t ht
      refine ⟨fun i => le_trans hγ.le (ht.1 i), fun i => ?_⟩
      have h0 : ∀ i ∈ Finset.univ, 0 ≤ t i := fun i _ => le_trans hγ.le (ht.1 i)
      have := Finset.single_le_sum h0 (Finset.mem_univ i)
      simp only [Pi.one_apply]; linarith [ht.2]
    have hvol : volume s ≤ 1 := by
      calc volume s ≤ volume (Set.Icc (0 : Fin (j + 1) → ℝ) 1) := measure_mono hsub
        _ = 1 := by simp [Real.volume_Icc_pi]
    have hbound : ∀ t ∈ s, ‖(w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹‖ ≤ (1 / γ) ^ (j + 2) := by
      intro t ht
      have h1 : γ ≤ w - ∑ i, t i := by linarith [ht.2]
      rw [norm_mul, norm_prod, show j + 2 = (j + 1) + 1 by rfl, pow_succ']
      apply mul_le_mul
      · rw [norm_inv, Real.norm_eq_abs, abs_of_pos (hγ.trans_le h1), ← one_div]
        exact one_div_le_one_div_of_le hγ h1
      · calc ∏ i, ‖(t i)⁻¹‖ ≤ ∏ _i : Fin (j + 1), 1 / γ := by
              apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
              intro i _
              rw [norm_inv, Real.norm_eq_abs, abs_of_pos (hγ.trans_le (ht.1 i)), ← one_div]
              exact one_div_le_one_div_of_le hγ (ht.1 i)
          _ = (1 / γ) ^ (j + 1) := by simp
      · exact Finset.prod_nonneg fun i _ => norm_nonneg _
      · positivity
    have hint := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (hvol.trans_lt ENNReal.one_lt_top) hbound
    have hreal : volume.real s ≤ 1 := by
      unfold Measure.real
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hvol)
    rw [Real.norm_eq_abs] at hint
    have hI : |∫ t in s, (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹| ≤ (1 / γ) ^ (j + 2) :=
      calc _ ≤ (1 / γ) ^ (j + 2) * volume.real s := hint
        _ ≤ (1 / γ) ^ (j + 2) * 1 := by gcongr
        _ = _ := mul_one _
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / ((j + 2).factorial : ℝ) * |∫ t in s, (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹|
        ≤ 1 / ((j + 2).factorial : ℝ) * (1 / γ) ^ (j + 2) := by gcongr
      _ = _ := by ring

lemma roughDensity_abs_le (γ w : ℝ) (hγ : 0 < γ) (hγw : γ ≤ w) (hw : w ≤ 1) :
    |roughDensity γ w| ≤ ∑' j : ℕ, (1 / γ) ^ j / (j.factorial : ℝ) := by
  have hg : Summable (fun j : ℕ => (1 / γ) ^ j / (j.factorial : ℝ)) :=
    Real.summable_pow_div_factorial _
  have hb := roughDensityTerm_abs_le γ w hγ hγw hw
  have hfn : Summable (fun j => ‖roughDensityTerm γ w j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => by simpa using hb j) hg
  unfold roughDensity
  rw [← Real.norm_eq_abs]
  calc ‖∑' j, roughDensityTerm γ w j‖ ≤ ∑' j, ‖roughDensityTerm γ w j‖ :=
        norm_tsum_le_tsum_norm hfn
    _ ≤ _ := Summable.tsum_le_tsum (fun j => by simpa using hb j) hfn hg

/-! ## The Mertens product at the sieve level -/

lemma mertensProduct_nonneg (y : ℝ) : 0 ≤ mertensProduct y := by
  unfold mertensProduct
  apply Finset.prod_nonneg
  intro p hp
  have : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt
  rw [sub_nonneg, div_le_one (by linarith)]; exact this.le

lemma tendsto_sieveLevel : Tendsto sieveLevel atTop atTop :=
  Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop)

lemma eventually_LV : ∃ c > 0, ∀ᶠ x in atTop, c ≤ log x * mertensProduct (sieveLevel x) := by
  set c0 := exp (-eulerMascheroniConstant)
  have hc0 : 0 < c0 := exp_pos _
  refine ⟨c0 / 2, by positivity, ?_⟩
  have h1 := mertens_product.eventually (eventually_gt_nhds (by linarith : c0 / 2 < c0))
  filter_upwards [tendsto_sieveLevel.eventually h1,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hL
  have hlog : log (sieveLevel x) = log x ^ (0.24 : ℝ) := by unfold sieveLevel; exact Real.log_exp _
  simp only [hlog] at hx
  have h2 : log x ^ (0.24 : ℝ) ≤ log x := by
    calc log x ^ (0.24 : ℝ) ≤ log x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ = log x := Real.rpow_one _
  have h3 := mertensProduct_nonneg (sieveLevel x)
  nlinarith

lemma eventually_proxy_bound (γ : ℝ) (hγ : 0 < γ) : ∃ Cα : ℝ, 0 ≤ Cα ∧ ∀ᶠ x in atTop, ∀ w : ℝ, γ ≤ w →
    w ≤ 1 → |roughDensity γ w / (log x * mertensProduct (sieveLevel x))| ≤ Cα := by
  obtain ⟨c, hc, hev⟩ := eventually_LV
  set R := ∑' j : ℕ, (1 / γ) ^ j / (j.factorial : ℝ)
  refine ⟨R / c, div_nonneg (tsum_nonneg fun j => by positivity) hc.le, ?_⟩
  filter_upwards [hev] with x hx w hw1 hw2
  rw [abs_div, abs_of_pos (hc.trans_le hx)]
  have hR := roughDensity_abs_le γ w hγ hw1 hw2
  exact div_le_div₀ ((abs_nonneg _).trans hR) hR hc hx

/-! ## The coefficient `(10.13)` -/

open Classical in
/-- The coefficient `1_J(m) m^{iv} (R_γ(m) - B_γ(m))` of Proposition 10.3. -/
noncomputable def coefN (γ x : ℝ) (J : Set ℝ) (v : ℝ) (m : ℕ) : ℂ :=
  if (m : ℝ) ∈ J then
    (m : ℂ) ^ (Complex.I * v) *
      ((if IsRough (x ^ γ) m then 1 else 0) -
        ((roughDensity γ (log m / log x) /
            (log x * mertensProduct (sieveLevel x)) : ℝ) : ℂ) *
          (if IsRough (sieveLevel x) m then 1 else 0))
  else 0

lemma isRough_mono {y y' : ℝ} {m : ℕ} (h : IsRough y m) (hy : y' ≤ y) : IsRough y' m :=
  ⟨h.1, fun p hp => lt_of_le_of_lt hy (h.2 p hp)⟩

lemma coefN_support {γ x : ℝ} {J : Set ℝ} {v : ℝ} {m : ℕ} (hW : sieveLevel x ≤ x ^ γ)
    (h : coefN γ x J v m ≠ 0) : (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m := by
  classical
  unfold coefN at h
  by_cases hJ : (m : ℝ) ∈ J
  · refine ⟨hJ, ?_⟩
    by_contra hRW
    have hR : ¬ IsRough (x ^ γ) m := fun hR => hRW (isRough_mono hR hW)
    rw [if_pos hJ, if_neg hR, if_neg hRW] at h
    simp at h
  · rw [if_neg hJ] at h; exact absurd rfl h

lemma norm_coefN_le {γ x Cα : ℝ} {J : Set ℝ} {v : ℝ} {m : ℕ} (hm : 0 < m)
    (hρ : |roughDensity γ (log m / log x) / (log x * mertensProduct (sieveLevel x))| ≤ Cα) :
    ‖coefN γ x J v m‖ ≤ 1 + Cα := by
  classical
  have hC : 0 ≤ Cα := (abs_nonneg _).trans hρ
  unfold coefN
  by_cases hJ : (m : ℝ) ∈ J
  · rw [if_pos hJ, norm_mul, Complex.norm_natCast_cpow_of_pos hm]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, Real.rpow_zero, one_mul]
    have ha : ∀ P : Prop, [Decidable P] → ‖(if P then (1 : ℂ) else 0)‖ ≤ 1 := by
      intro P _; split_ifs <;> simp
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := ha (IsRough (sieveLevel x) m)
    have h2 := ha (IsRough (x ^ γ) m)
    have h3 := abs_nonneg (roughDensity γ (log m / log x) /
      (log x * mertensProduct (sieveLevel x)))
    have h4 := norm_nonneg (if IsRough (sieveLevel x) m then (1 : ℂ) else 0)
    calc _ ≤ 1 + Cα * 1 := by gcongr
      _ = 1 + Cα := by ring
  · rw [if_neg hJ]; simp; linarith


lemma coefN_zero_eq {γ x : ℝ} {J : Set ℝ} {m : ℕ} (hmJ : (m : ℝ) ∈ J) :
    coefN γ x J 0 m = ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) := by
  unfold coefN roughIndicator roughProxy
  rw [if_pos hmJ]
  simp only [Complex.ofReal_zero, mul_zero, Complex.cpow_zero, one_mul]
  split_ifs <;> push_cast <;> ring

lemma coefN_not_mem {γ x v : ℝ} {J : Set ℝ} {m : ℕ} (hmJ : (m : ℝ) ∉ J) :
    coefN γ x J v m = 0 := by
  unfold coefN; rw [if_neg hmJ]

lemma norm_coefN_le' {γ x Cα Hm sMinus sPlus v : ℝ} {J : Set ℝ}
    (hρ : ∀ w : ℝ, γ ≤ w → w ≤ 1 →
      |roughDensity γ w / (log x * mertensProduct (sieveLevel x))| ≤ Cα)
    (hC : 0 ≤ Cα) (hL0 : 0 < log x) (hHm : 0 < Hm) (hJs : J ⊆ Set.Icc Hm (2 * Hm))
    (hγs : γ < sMinus) (hs1 : sMinus ≤ log Hm / log x) (hs2 : log (2 * Hm) / log x ≤ sPlus)
    (hsP : sPlus < 1) (m : ℕ) : ‖coefN γ x J v m‖ ≤ 1 + Cα := by
  by_cases hmJ : (m : ℝ) ∈ J
  · have hmI := hJs hmJ
    have hm0 : 0 < m := by
      have : (0 : ℝ) < m := lt_of_lt_of_le hHm hmI.1
      exact_mod_cast this
    have hwa : γ ≤ log m / log x := by
      rw [le_div_iff₀ hL0]
      have := Real.log_le_log hHm hmI.1
      rw [le_div_iff₀ hL0] at hs1
      nlinarith
    have hwb : log m / log x ≤ 1 := by
      rw [div_le_iff₀ hL0]
      have := Real.log_le_log (lt_of_lt_of_le hHm hmI.1) hmI.2
      rw [div_le_iff₀ hL0] at hs2
      nlinarith
    exact norm_coefN_le hm0 (hρ _ hwa hwb)
  · rw [coefN_not_mem hmJ, norm_zero]; linarith

/-! ## Cutting the dyadic ranges into short pieces -/

/-- The index of the short piece of `[H, 2H]` (of length `H/N`) containing `y`. -/
noncomputable def idx (H : ℝ) (N : ℕ) (y : ℝ) : ℕ := ⌊(N : ℝ) * (y / H - 1)⌋₊

/-- The left end point of the `i`-th piece. -/
noncomputable def ctr (H : ℝ) (N : ℕ) (i : ℕ) : ℝ := H * (1 + i / N)

/-- The `i`-th piece of `J`. -/
def cell (J : Set ℝ) (H : ℝ) (N : ℕ) (i : ℕ) : Set ℝ := J ∩ idx H N ⁻¹' {i}

lemma idx_mono {H : ℝ} (hH : 0 < H) (N : ℕ) : Monotone (idx H N) := by
  intro a b hab
  unfold idx
  apply Nat.floor_le_floor
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  have := div_le_div_of_nonneg_right hab hH.le
  linarith

lemma idx_le {H : ℝ} (hH : 0 < H) (N : ℕ) {y : ℝ} (hy : y ≤ 2 * H) : idx H N y ≤ N := by
  unfold idx
  apply Nat.floor_le_of_le
  have : y / H - 1 ≤ 1 := by
    have := (div_le_iff₀ hH).mpr (show y ≤ 2 * H by linarith); linarith
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

lemma ctr_close {H : ℝ} (hH : 0 < H) {N : ℕ} (hN : 0 < N) {y : ℝ} (hy : H ≤ y) :
    H ≤ ctr H N (idx H N y) ∧ ctr H N (idx H N y) ≤ y ∧ y ≤ ctr H N (idx H N y) + H / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set t := (N : ℝ) * (y / H - 1) with ht
  have ht0 : 0 ≤ t := by
    apply mul_nonneg hN'.le
    rw [sub_nonneg, le_div_iff₀ hH]; linarith
  have h1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
  have h2 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
  have hy' : y = H * (1 + t / N) := by
    rw [ht]; field_simp; ring
  unfold ctr idx
  rw [← ht]
  refine ⟨?_, ?_, ?_⟩
  · have : (0 : ℝ) ≤ ⌊t⌋₊ / N := by positivity
    nlinarith
  · rw [hy']
    apply mul_le_mul_of_nonneg_left _ hH.le
    gcongr
  · rw [hy']
    have : t / N ≤ ⌊t⌋₊ / N + 1 / N := by
      rw [← add_div]; exact div_le_div_of_nonneg_right h2.le hN'.le
    have : H * (1 + t / N) ≤ H * (1 + (⌊t⌋₊ / N + 1 / N)) :=
      mul_le_mul_of_nonneg_left (by linarith) hH.le
    calc H * (1 + t / N) ≤ H * (1 + (⌊t⌋₊ / N + 1 / N)) := this
      _ = H * (1 + ⌊t⌋₊ / N) + H / N := by ring

lemma cell_ordConnected {J : Set ℝ} (hJ : J.OrdConnected) {H : ℝ} (hH : 0 < H) (N i : ℕ) :
    (cell J H N i).OrdConnected :=
  hJ.inter (Set.ordConnected_singleton.preimage_mono (idx_mono hH N))

lemma coefN_cell (γ x v : ℝ) (J : Set ℝ) (H : ℝ) (N i m : ℕ) :
    coefN γ x (cell J H N i) v m = if idx H N m = i then coefN γ x J v m else 0 := by
  by_cases hmJ : (m : ℝ) ∈ J
  · by_cases hi : idx H N m = i
    · rw [if_pos hi]
      unfold coefN
      rw [if_pos hmJ, if_pos ⟨hmJ, hi⟩]
    · rw [if_neg hi, coefN_not_mem]
      exact fun h => hi h.2
  · rw [coefN_not_mem (fun h => hmJ h.1), coefN_not_mem hmJ, ite_self]

lemma psi_diff {Ψ : ℝ → ℝ} {Lip : NNReal} (hLip : LipschitzWith Lip Ψ) {x c₂ Hm Hn m n : ℝ}
    {N : ℕ} (hN : 0 < N) (hx : 0 < x) (hHm : 0 < Hm) (hHn : 0 < Hn) (hm1 : Hm ≤ m)
    (hm2 : m ≤ 2 * Hm) (hn1 : Hn ≤ n) (hn2 : n ≤ 2 * Hn) (hX : Hm * Hn ≤ c₂ * x) :
    ‖(Ψ (m * n / x) : ℂ) - (Ψ (ctr Hm N (idx Hm N m) * ctr Hn N (idx Hn N n) / x) : ℂ)‖ ≤
      Lip * (4 * c₂ / N) := by
  obtain ⟨a0, a1, a2⟩ := ctr_close hHm hN hm1
  obtain ⟨b0, b1, b2⟩ := ctr_close hHn hN hn1
  set m' := ctr Hm N (idx Hm N m)
  set n' := ctr Hn N (idx Hn N n)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hd := hLip.dist_le_mul (m * n / x) (m' * n' / x)
  rw [Real.dist_eq, Real.dist_eq] at hd
  refine hd.trans (mul_le_mul_of_nonneg_left ?_ Lip.2)
  rw [← sub_div, abs_div, abs_of_pos hx, div_le_iff₀ hx]
  have e1 : m * n - m' * n' = (m - m') * n + m' * (n - n') := by ring
  have hA : (m - m') * n ≤ Hm / N * (2 * Hn) :=
    mul_le_mul (by linarith) hn2 (by linarith) (by positivity)
  have hB : m' * (n - n') ≤ (2 * Hm) * (Hn / N) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hA0 : 0 ≤ (m - m') * n := mul_nonneg (by linarith) (by linarith)
  have hB0 : 0 ≤ m' * (n - n') := mul_nonneg (by linarith) (by linarith)
  rw [abs_of_nonneg (by rw [e1]; linarith), e1]
  have : Hm / N * (2 * Hn) + (2 * Hm) * (Hn / N) = 4 * (Hm * Hn) / N := by ring
  have h4 : 4 * (Hm * Hn) / N ≤ 4 * c₂ / N * x := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hN']; linarith
  linarith

/-! ## Algebra of the decomposition -/

lemma sum5_comm {A B C D E : Type*} (s1 : Finset A) (s2 : Finset B) (s3 : Finset C)
    (s4 : Finset D) (s5 : Finset E) (f : A → B → C → D → E → ℂ) :
    ∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, ∑ e ∈ s5, f a b c d e =
      ∑ d ∈ s4, ∑ e ∈ s5, ∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, f a b c d e := by
  calc _ = ∑ a ∈ s1, ∑ b ∈ s2, ∑ d ∈ s4, ∑ c ∈ s3, ∑ e ∈ s5, f a b c d e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a ∈ s1, ∑ b ∈ s2, ∑ d ∈ s4, ∑ e ∈ s5, ∑ c ∈ s3, f a b c d e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ a ∈ s1, ∑ d ∈ s4, ∑ b ∈ s2, ∑ e ∈ s5, ∑ c ∈ s3, f a b c d e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a ∈ s1, ∑ d ∈ s4, ∑ e ∈ s5, ∑ b ∈ s2, ∑ c ∈ s3, f a b c d e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ d ∈ s4, ∑ a ∈ s1, ∑ e ∈ s5, ∑ b ∈ s2, ∑ c ∈ s3, f a b c d e := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun d _ => Finset.sum_comm

lemma main_identity (M : ℕ) (hM : 0 < M) (u : ℤ) (hu : IsCoprime u M) (R1 R2 : Finset ℕ)
    (N : ℕ) (coef b : ℕ → ℂ) (g : ℕ → ℕ → ℂ) (ι₁ ι₂ : ℕ → ℕ) (Ψc : ℕ → ℕ → ℂ)
    (h1 : ∀ m ∈ R1, coef m ≠ 0 → ι₁ m ∈ Finset.range (N + 1))
    (h2 : ∀ n ∈ R2, b n ≠ 0 → ι₂ n ∈ Finset.range (N + 1)) :
    ∑ m ∈ R1, ∑ n ∈ R2, coef m * b n *
        ((if ((m * n : ℕ) : ℤ) ≡ u [ZMOD M] then (1 : ℂ) else 0) * Ψc (ι₁ m) (ι₂ n) * g m n) =
      ∑ l : DirichletCharacter ℂ M, ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        ((M.totient : ℂ)⁻¹ * l ((u : ZMod M))⁻¹ * Ψc i j) *
          ∑ m ∈ R1, ∑ n ∈ R2, ((if ι₁ m = i then coef m else 0) * l (m : ZMod M)) *
            (if ι₂ n = j then b n * l (n : ZMod M) else 0) * g m n := by
  simp_rw [Finset.mul_sum]
  rw [sum5_comm]
  apply Finset.sum_congr rfl; intro m hm; apply Finset.sum_congr rfl; intro n hn
  by_cases hc : coef m = 0
  · simp [hc]
  by_cases hb : b n = 0
  · simp [hb]
  have hred : ∀ l : DirichletCharacter ℂ M,
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        ((M.totient : ℂ)⁻¹ * l ((u : ZMod M))⁻¹ * Ψc i j) *
          (((if ι₁ m = i then coef m else 0) * l (m : ZMod M)) *
            (if ι₂ n = j then b n * l (n : ZMod M) else 0) * g m n) =
      ((M.totient : ℂ)⁻¹ * l ((u : ZMod M))⁻¹ * Ψc (ι₁ m) (ι₂ n)) *
          ((coef m * l (m : ZMod M)) * (b n * l (n : ZMod M)) * g m n) := by
    intro l
    rw [Finset.sum_eq_single_of_mem (ι₁ m) (h1 m hm hc)]
    · rw [Finset.sum_eq_single_of_mem (ι₂ n) (h2 n hn hb)]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
    · intro i _ hi; simp [Ne.symm hi]
  rw [Finset.sum_congr rfl (fun l _ => hred l), char_indicator M hM u hu m n, Finset.sum_mul,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro l _; ring

lemma norm_sum3_le {Λ : Type*} [Fintype Λ] (N : ℕ) (f : Λ → ℕ → ℕ → ℂ) (B : ℝ)
    (hf : ∀ l i j, ‖f l i j‖ ≤ B) :
    ‖∑ l : Λ, ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), f l i j‖ ≤
      Fintype.card Λ * ((N + 1) * ((N + 1) * B)) := by
  refine (norm_sum_le _ _).trans ?_
  have : ∀ l, ‖∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), f l i j‖ ≤
      (N + 1) * ((N + 1) * B) := by
    intro l
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i, ‖∑ j ∈ Finset.range (N + 1), f l i j‖ ≤ (N + 1) * B := by
      intro i
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun j _ => hf l i j).trans ?_
      simp
    refine (Finset.sum_le_sum fun i _ => this i).trans ?_
    simp
  refine (Finset.sum_le_sum fun l _ => this l).trans ?_
  simp

lemma norm_sum2_le (R1 R2 : Finset ℕ) (f : ℕ → ℕ → ℂ) (B : ℝ)
    (hf : ∀ m ∈ R1, ∀ n ∈ R2, ‖f m n‖ ≤ B) :
    ‖∑ m ∈ R1, ∑ n ∈ R2, f m n‖ ≤ R1.card * (R2.card * B) := by
  refine (norm_sum_le _ _).trans ?_
  have : ∀ m ∈ R1, ‖∑ n ∈ R2, f m n‖ ≤ R2.card * B := by
    intro m hm
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun n hn => hf m hm n hn).trans ?_
    simp
  refine (Finset.sum_le_sum this).trans ?_
  simp


open Classical in
lemma core (M c : ℕ) (u : ℤ) (hM : 0 < M) (hu : IsCoprime u M) (Ψ : ℝ → ℝ)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (Lip : NNReal) (hLip : LipschitzWith Lip Ψ)
    (γ sMinus sPlus Cα c₁ c₂ : ℝ) (hγs : γ < sMinus) (hsPlus : sPlus < 1) (hCα0 : 0 ≤ Cα)
    (hc₁ : 0 < c₁) {K : ℕ} (a : Fin K → ℝ) (A₁ x Hm Hn : ℝ) (J : Set ℝ) (b : ℕ → ℂ)
    (hρ : ∀ w : ℝ, γ ≤ w → w ≤ 1 →
      |roughDensity γ w / (log x * mertensProduct (sieveLevel x))| ≤ Cα)
    (hxV : ∀ i, 1 / 2 ≤ groupReciprocalSum x (a i)) (hx1 : 1 < x) (hL1 : 1 ≤ log x)
    (hW : sieveLevel x ≤ x ^ γ) (hHm : 2 ≤ Hm) (hHn : 2 ≤ Hn) (h3 : c₁ * x ≤ Hm * Hn)
    (h4 : Hm * Hn ≤ c₂ * x) (hJs : J ⊆ Set.Icc Hm (2 * Hm))
    (hs1 : sMinus ≤ log Hm / log x) (hs2 : log (2 * Hm) / log x ≤ sPlus)
    (hb1' : ∀ n, ‖b n‖ ≤ 1)
    (hb1 : ∀ n, b n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n)
    (hBilRaw : ∀ (l : DirichletCharacter ℂ M) (i j : ℕ),
      ‖∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
          coefN γ x (cell J Hm ⌈log x ^ (6 : ℝ)⌉₊ i) 0 m * l (m : ZMod M) *
            (if idx Hn ⌈log x ^ (6 : ℝ)⌉₊ n = j then b n * l (n : ZMod M) else 0) *
            (predecessorIndicator x a c (m * n - 1) : ℂ) *
            (mark (1 / 2) x a (m * n - 1) : ℂ)‖ ≤
        A₁ * (Hm * Hn) * log x ^ (-(18 : ℝ))) :
    ‖∑ m ∈ (Finset.range (⌊2 * Hm⌋₊ + 1)).filter (fun m : ℕ => (m : ℝ) ∈ J),
          ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
          ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) * b n *
            (constructionWeight M c u Ψ x a (m * n) : ℂ)‖ ≤
      (9 * (Fintype.card (DirichletCharacter ℂ M) : ℝ) * max A₁ 0 +
        9 * ((1 + Cα) * (Lip * (4 * c₂)) * 2 ^ K)) * (Hm * Hn) * log x ^ (-6 : ℝ) := by
  set nl : ℝ := (Fintype.card (DirichletCharacter ℂ M) : ℝ) with hnl
  set A₁' := max A₁ 0 with hA₁'
  set τ₀ : ℝ := (1 + Cα) * (Lip * (4 * c₂)) * 2 ^ K with hτ₀
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < log x := by linarith
  have hX0 : 0 < Hm * Hn := by positivity
  have hc₂ : 0 ≤ c₂ := by
    by_contra hneg; push Not at hneg; nlinarith
  set N : ℕ := ⌈log x ^ (6 : ℝ)⌉₊ with hN
  set P6 : ℝ := log x ^ (6 : ℝ) with hP6
  have hL6 : 1 ≤ P6 := Real.one_le_rpow hL1 (by norm_num)
  have hNge : P6 ≤ N := Nat.le_ceil _
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := by linarith
    exact_mod_cast this
  have hNle : (N : ℝ) + 1 ≤ 3 * P6 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ P6 by linarith); linarith
  set R1 := Finset.range (⌊2 * Hm⌋₊ + 1) with hR1
  set R2 := Finset.range (⌊2 * Hn⌋₊ + 1) with hR2
  set coef := coefN γ x J 0 with hcoef
  set ind : ℕ → ℕ → ℂ := fun m n =>
    if ((m * n : ℕ) : ℤ) ≡ u [ZMOD M] then (1 : ℂ) else 0 with hind
  set g : ℕ → ℕ → ℂ := fun m n => G x a c (m * n - 1) with hg
  set Ψc : ℕ → ℕ → ℂ := fun i j => (Ψ (ctr Hm N i * ctr Hn N j / x) : ℂ) with hΨc
  have hcoef_supp : ∀ m, coef m ≠ 0 → (m : ℝ) ∈ J := fun m h => (coefN_support hW h).1
  -- Step 1: the target as a sum with the coefficient and the expanded weight
  have hT1 : ∑ m ∈ R1.filter (fun m : ℕ => (m : ℝ) ∈ J), ∑ n ∈ R2,
        ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) * b n *
          (constructionWeight M c u Ψ x a (m * n) : ℂ) =
      ∑ m ∈ R1, ∑ n ∈ R2, coef m * b n * (ind m n * (Ψ (((m * n : ℕ) : ℝ) / x) : ℂ) * g m n) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro m _
    by_cases hmJ : (m : ℝ) ∈ J
    · rw [if_pos hmJ]; apply Finset.sum_congr rfl; intro n _
      rw [← coefN_zero_eq hmJ]
      by_cases hb : b n = 0
      · simp [hb]
      have hmI := hJs hmJ
      have hnI := hb1 n hb
      have hm2 : 2 ≤ m := by
        have : (2 : ℝ) ≤ m := le_trans hHm hmI.1
        exact_mod_cast this
      have hn1 : 1 ≤ n := by
        have : (1 : ℝ) ≤ n := by linarith [hnI.1]
        exact_mod_cast this
      have h2mn : 2 ≤ m * n := by nlinarith
      unfold constructionWeight
      simp only [hind, hg, G]
      by_cases hcong : ((m * n : ℕ) : ℤ) ≡ u [ZMOD M]
      · rw [if_pos ⟨h2mn, hcong⟩, if_pos hcong]; push_cast; ring
      · rw [if_neg (fun h => hcong h.2), if_neg hcong]; simp
    · rw [if_neg hmJ]; symm; apply Finset.sum_eq_zero; intro n _
      simp [hcoef, coefN_not_mem hmJ]
  -- Step 2: split off the variation of `Ψ` on the short pieces
  have hT2 : ∑ m ∈ R1, ∑ n ∈ R2, coef m * b n *
        (ind m n * (Ψ (((m * n : ℕ) : ℝ) / x) : ℂ) * g m n) =
      ∑ m ∈ R1, ∑ n ∈ R2, coef m * b n *
        (ind m n * Ψc (idx Hm N m) (idx Hn N n) * g m n) +
      ∑ m ∈ R1, ∑ n ∈ R2, coef m * b n *
        (ind m n * ((Ψ (((m * n : ℕ) : ℝ) / x) : ℂ) - Ψc (idx Hm N m) (idx Hn N n)) * g m n) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro m _
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro n _
    ring
  have hMainEq := main_identity M hM u hu R1 R2 N coef b g (fun m : ℕ => idx Hm N m) (fun n : ℕ => idx Hn N n) Ψc
    (fun m _ hm => Finset.mem_range.mpr (Nat.lt_succ_of_le
      (idx_le (by linarith) N (hJs (hcoef_supp m hm)).2)))
    (fun n _ hn => Finset.mem_range.mpr (Nat.lt_succ_of_le
      (idx_le (by linarith) N (hb1 n hn).2.1)))
  -- the bilinear pieces, by Lemma 10.2
  have hBil : ∀ (l : DirichletCharacter ℂ M) (i j : ℕ),
      ‖((M.totient : ℂ)⁻¹ * l ((u : ZMod M))⁻¹ * Ψc i j) *
          ∑ m ∈ R1, ∑ n ∈ R2, ((if idx Hm N m = i then coef m else 0) * l (m : ZMod M)) *
            (if idx Hn N n = j then b n * l (n : ZMod M) else 0) * g m n‖ ≤
        A₁' * (Hm * Hn) * (P6 ^ 3)⁻¹ := by
    intro l i j
    have hB := hBilRaw l i j
    have hsum : ∑ m ∈ R1, ∑ n ∈ R2, ((if idx Hm N m = i then coef m else 0) * l (m : ZMod M)) *
            (if idx Hn N n = j then b n * l (n : ZMod M) else 0) * g m n =
        ∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
          coefN γ x (cell J Hm N i) 0 m * l (m : ZMod M) *
            (if idx Hn N n = j then b n * l (n : ZMod M) else 0) *
            (predecessorIndicator x a c (m * n - 1) : ℂ) *
            (mark (1 / 2) x a (m * n - 1) : ℂ) := by
      apply Finset.sum_congr rfl; intro m _; apply Finset.sum_congr rfl; intro n _
      simp only [coefN_cell, hcoef, hg, G]
      ring
    have hcl : ‖(M.totient : ℂ)⁻¹ * l ((u : ZMod M))⁻¹ * Ψc i j‖ ≤ 1 := by
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
      have e1 : ((M.totient : ℕ) : ℝ)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by exact_mod_cast Nat.totient_pos.mpr hM)
      have e2 := DirichletCharacter.norm_le_one l ((u : ZMod M))⁻¹
      have e3 : ‖Ψc i j‖ ≤ 1 := by
        simp only [hΨc, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (hΨ0 _)]; exact hΨ1 _
      calc _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul e1 e2 (norm_nonneg _) zero_le_one) e3
            (norm_nonneg _) (by norm_num)
        _ = 1 := by ring
    have e18 : log x ^ (-(18 : ℝ)) = (P6 ^ 3)⁻¹ := by
      rw [Real.rpow_neg hL0.le, show (18 : ℝ) = 6 * ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_mul hL0.le, Real.rpow_natCast]
    rw [norm_mul, hsum]
    calc _ ≤ 1 * (A₁ * (Hm * Hn) * log x ^ (-(18 : ℝ))) :=
          mul_le_mul hcl hB (norm_nonneg _) zero_le_one
      _ ≤ A₁' * (Hm * Hn) * (P6 ^ 3)⁻¹ := by
          rw [one_mul, e18]
          gcongr
          exact le_max_left _ _
  have hMain : ‖∑ m ∈ R1, ∑ n ∈ R2, coef m * b n *
        (ind m n * Ψc (idx Hm N m) (idx Hn N n) * g m n)‖ ≤ 9 * nl * A₁' * (Hm * Hn) * P6⁻¹ := by
    rw [hMainEq]
    refine (norm_sum3_le N _ _ hBil).trans ?_
    have hA0 : 0 ≤ A₁' := le_max_right _ _
    have hP : 0 < P6 := by linarith
    have hnl : 0 ≤ nl := Nat.cast_nonneg _
    have hB0 : 0 ≤ A₁' * (Hm * Hn) * (P6 ^ 3)⁻¹ := by positivity
    calc _ ≤ nl * ((3 * P6) * ((3 * P6) * (A₁' * (Hm * Hn) * (P6 ^ 3)⁻¹))) := by
          gcongr
      _ = 9 * nl * A₁' * (Hm * Hn) * P6⁻¹ := by field_simp; ring
  have hErr : ‖∑ m ∈ R1, ∑ n ∈ R2, coef m * b n *
        (ind m n * ((Ψ (((m * n : ℕ) : ℝ) / x) : ℂ) - Ψc (idx Hm N m) (idx Hn N n)) * g m n)‖ ≤
      9 * τ₀ * (Hm * Hn) * P6⁻¹ := by
    have hτ : ∀ m ∈ R1, ∀ n ∈ R2, ‖coef m * b n *
        (ind m n * ((Ψ (((m * n : ℕ) : ℝ) / x) : ℂ) - Ψc (idx Hm N m) (idx Hn N n)) * g m n)‖ ≤
        (1 + Cα) * (Lip * (4 * c₂ / N)) * 2 ^ K := by
      intro m _ n _
      have hτ0 : 0 ≤ (1 + Cα) * (Lip * (4 * c₂ / N)) * 2 ^ K := by
        have := Lip.2; positivity
      by_cases hc0 : coef m = 0
      · rw [hc0, zero_mul, zero_mul, norm_zero]; exact hτ0
      by_cases hb0 : b n = 0
      · rw [hb0, mul_zero, zero_mul, norm_zero]; exact hτ0
      have hmI := hJs (hcoef_supp m hc0)
      have hnI := hb1 n hb0
      have e1 : ‖coef m‖ ≤ 1 + Cα :=
        norm_coefN_le' hρ hCα0 hL0 (by linarith) hJs hγs hs1 hs2 hsPlus m
      have e2 : ‖ind m n‖ ≤ 1 := by simp only [hind]; split_ifs <;> simp
      have e3 : ‖(Ψ (((m * n : ℕ) : ℝ) / x) : ℂ) - Ψc (idx Hm N m) (idx Hn N n)‖ ≤
          Lip * (4 * c₂ / N) := by
        simp only [hΨc]; push_cast
        exact psi_diff hLip hNpos hx0 (by linarith) (by linarith) hmI.1 hmI.2 hnI.1 hnI.2.1 h4
      have e4 : ‖g m n‖ ≤ 2 ^ K := norm_G_le x a c _ hxV
      rw [norm_mul, norm_mul, norm_mul, norm_mul]
      calc _ ≤ ((1 + Cα) * 1) * ((1 * (Lip * (4 * c₂ / N))) * 2 ^ K) := by
            gcongr
            exact hb1' n
        _ = _ := by ring
    refine (norm_sum2_le R1 R2 _ _ hτ).trans ?_
    have hc1 : (R1.card : ℝ) ≤ 3 * Hm := by
      rw [hR1, Finset.card_range]; push_cast
      have := Nat.floor_le (show (0 : ℝ) ≤ 2 * Hm by linarith); linarith
    have hc2 : (R2.card : ℝ) ≤ 3 * Hn := by
      rw [hR2, Finset.card_range]; push_cast
      have := Nat.floor_le (show (0 : ℝ) ≤ 2 * Hn by linarith); linarith
    have hP : 0 < P6 := by linarith
    have hNinv : (4 * c₂ / N) ≤ 4 * c₂ * P6⁻¹ := by
      rw [div_eq_mul_inv]; gcongr
    have hLip0 := Lip.2
    calc _ ≤ (3 * Hm) * ((3 * Hn) * ((1 + Cα) * (Lip * (4 * c₂ * P6⁻¹)) * 2 ^ K)) := by
          gcongr
      _ = 9 * τ₀ * (Hm * Hn) * P6⁻¹ := by rw [hτ₀]; ring
  have e6 : log x ^ (-6 : ℝ) = P6⁻¹ := by rw [Real.rpow_neg hL0.le]
  rw [hT1, hT2, e6]
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ 9 * nl * A₁' * (Hm * Hn) * P6⁻¹ + 9 * τ₀ * (Hm * Hn) * P6⁻¹ := add_le_add hMain hErr
    _ = _ := by ring

end ArtinPrimitiveRoots.TypeIIProg

open ArtinPrimitiveRoots ArtinPrimitiveRoots.TypeIIProg Real Filter in
open Classical in
theorem solution (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y)
    (δ γ sMinus sPlus : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hγs : γ < sMinus) (hss : sMinus < sPlus) (hsPlus : sPlus < 1)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) :
    ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ A : ℝ, ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ Hm Hn : ℝ, x ^ δ ≤ Hm → x ^ δ ≤ Hn → c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc Hm (2 * Hm) →
      sMinus ≤ log Hm / log x → log (2 * Hm) / log x ≤ sPlus →
      ∀ b : ℕ → ℂ, (∀ n, ‖b n‖ ≤ 1) →
        (∀ n, b n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
      ‖∑ m ∈ (Finset.range (⌊2 * Hm⌋₊ + 1)).filter (fun m : ℕ => (m : ℝ) ∈ J),
          ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
          ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) * b n *
            (constructionWeight M c u Ψ x a (m * n) : ℂ)‖ ≤
        A * (Hm * Hn) * log x ^ (-6 : ℝ) := by
  obtain ⟨Cα, hCα0, hCα⟩ := eventually_proxy_bound γ hγ
  have hcs : HasCompactSupport Ψ :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport Ψ)
      (hΨs.trans Set.Ioo_subset_Icc_self)
  obtain ⟨Lip, hLip⟩ := hΨ.lipschitzWith_of_hasCompactSupport hcs (by simp)
  have hlog76 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.76)).comp Real.tendsto_log_atTop
  have hxδ := tendsto_rpow_atTop hδ
  obtain ⟨X, hX⟩ := eventually_atTop.mp (hCα.and ((eventually_gt_atTop 1).and
    ((Real.tendsto_log_atTop.eventually_ge_atTop
      (max (max 1 (2 * c₂)) (max (M : ℝ) (1 + Cα)))).and
      ((hlog76.eventually_ge_atTop (1 / γ)).and (hxδ.eventually_ge_atTop 2)))))
  have hXfacts : ∀ x, X ≤ x → 1 < x ∧ 1 ≤ log x ∧ 2 * c₂ ≤ log x ∧ (M : ℝ) ≤ log x ∧
      1 + Cα ≤ log x ∧ sieveLevel x ≤ x ^ γ ∧ 2 ≤ x ^ δ := by
    intro x hx
    obtain ⟨-, h1, hL, h76, hδ2⟩ := hX x hx
    simp only [Function.comp] at h76
    refine ⟨h1, le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL,
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL,
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL,
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL, ?_, hδ2⟩
    have hL0 : 0 < log x := Real.log_pos h1
    unfold sieveLevel
    rw [show x ^ γ = exp (log x * γ) from Real.rpow_def_of_pos (by linarith) γ, Real.exp_le_exp]
    have hsplit : log x = log x ^ (0.24 : ℝ) * log x ^ (0.76 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    have h24 : 0 ≤ log x ^ (0.24 : ℝ) := by positivity
    have : log x ^ (0.24 : ℝ) * 1 ≤ log x ^ (0.24 : ℝ) * (log x ^ (0.76 : ℝ) * γ) := by
      apply mul_le_mul_of_nonneg_left _ h24
      rw [div_le_iff₀ hγ] at h76; linarith
    calc log x ^ (0.24 : ℝ) = log x ^ (0.24 : ℝ) * 1 := (mul_one _).symm
      _ ≤ _ := this
      _ = log x ^ (0.24 : ℝ) * log x ^ (0.76 : ℝ) * γ := by ring
      _ = log x * γ := by rw [← hsplit]
  -- the set of tuples fed to Lemma 10.2
  let P : ℝ → ℝ → ℝ → (ℕ → ℂ) → (ℕ → ℂ) → Prop := fun x Hm Hn α β =>
    X ≤ x ∧ x ^ δ ≤ Hm ∧ x ^ δ ≤ Hn ∧ c₁ * x ≤ Hm * Hn ∧ Hm * Hn ≤ c₂ * x ∧
    sMinus ≤ log Hm / log x ∧ log (2 * Hm) / log x ≤ sPlus ∧
    (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧ ∃ l : DirichletCharacter ℂ M,
      α = fun m => coefN γ x J 0 m * l (m : ZMod M)) ∧
    (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) ∧
    (∀ n, ‖β n‖ ≤ log x ^ (1 : ℝ))
  let S : Set (ℝ × ℝ × ℝ × (ℕ → ℂ) × (ℕ → ℂ)) :=
    {p | P p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2}
  have hS : ∀ x Hm Hn : ℝ, ∀ α β : ℕ → ℂ, (x, Hm, Hn, α, β) ∈ S →
      x ^ δ ≤ Hm ∧ x ^ δ ≤ Hn ∧ c₁ * x ≤ Hm * Hn ∧ Hm * Hn ≤ c₂ * x ∧
      (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
        ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) ∧
      (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) ∧
      (∀ m, ‖α m‖ ≤ log x ^ (1 : ℝ)) ∧ (∀ n, ‖β n‖ ≤ log x ^ (1 : ℝ)) := by
    rintro x Hm Hn α β ⟨hxX, h1, h2, h3, h4, hw1, hw2, ⟨J, hJ, hJs, l, hαe⟩, hβ1, hβ2⟩
    dsimp only at hαe hxX h1 h2 h3 h4 hw1 hw2 hβ1 hβ2 hJ hJs; subst hαe
    obtain ⟨hx1, hL1, -, -, hCL, hW, -⟩ := hXfacts x hxX
    refine ⟨h1, h2, h3, h4, ⟨J, hJ, hJs, fun m hm => ?_⟩, hβ1, fun m => ?_, hβ2⟩
    · apply coefN_support (v := 0) hW; intro h0; apply hm; simp [h0]
    · have hL0 : 0 < log x := by linarith
      have hHm : 0 < Hm := lt_of_lt_of_le (by positivity) h1
      dsimp only
      rw [norm_mul, Real.rpow_one]
      calc ‖coefN γ x J 0 m‖ * ‖l (m : ZMod M)‖ ≤ (1 + Cα) * 1 :=
            mul_le_mul (norm_coefN_le' (hX x hxX).1 hCα0 hL0 hHm hJs hγs hw1 hw2 hsPlus m)
              (DirichletCharacter.norm_le_one _ _) (norm_nonneg _) (by linarith)
        _ ≤ log x := by linarith
  have hα : ∀ A₀ B A : ℝ, 0 < A₀ → 0 < B → 0 < A →
      ∃ C' : ℝ, ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, ∀ α β : ℕ → ℂ, (x, Hm, Hn, α, β) ∈ S → x₀ ≤ x →
        ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
        ∀ t : ℝ, |t| ≤ 2 * (Hm * Hn) * log x ^ B →
          ‖((1 / Hm : ℝ) : ℂ) * ∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1),
              α m * χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * t)‖ ≤ C' * log x ^ (-A) := by
    intro A₀ B A hA₀ hB hA
    obtain ⟨C', x₀', hcb⟩ := rough_factor_coefficient_bound 1 γ sMinus sPlus one_pos hγ hγs hss
      hsPlus (A₀ + 1) (B + 1) A (by linarith) (by linarith) hA
    refine ⟨C', x₀', ?_⟩
    rintro x Hm Hn α β ⟨hxX, h1, h2, h3, h4, hw1, hw2, ⟨J, hJ, hJs, l, hαe⟩, hβ1, hβ2⟩
      hx k hk hkle χ t ht
    dsimp only at hαe hxX h1 h2 h3 h4 hw1 hw2 hβ1 hβ2 hJ hJs; subst hαe
    obtain ⟨hx1, hL1, hLc, hLM, -, -, -⟩ := hXfacts x hxX
    have hx0 : 0 < x := by linarith
    have hL0 : 0 < log x := by linarith
    have ht' : |t| ≤ x * log x ^ (B + 1) := by
      rw [Real.rpow_add_one hL0.ne']
      have hLB : 0 ≤ log x ^ B := by positivity
      calc |t| ≤ 2 * (Hm * Hn) * log x ^ B := ht
        _ ≤ 2 * (c₂ * x) * log x ^ B := by gcongr
        _ = (2 * c₂) * (x * log x ^ B) := by ring
        _ ≤ log x * (x * log x ^ B) := by gcongr
        _ = x * (log x ^ B * log x) := by ring
    have hk' : 0 < M * k := Nat.mul_pos hM hk
    have hkle' : ((M * k : ℕ) : ℝ) ≤ log x ^ (A₀ + 1) := by
      rw [Real.rpow_add_one hL0.ne', Nat.cast_mul, mul_comm]
      exact mul_le_mul hkle hLM (Nat.cast_nonneg _) (by positivity)
    have hv : |(0 : ℝ)| ≤ log x ^ (1 : ℝ) := by rw [abs_zero]; positivity
    have hcb' := hcb x hx Hm hw1 hw2 J hJ hJs 0 hv (M * k) hk' hkle'
      (DirichletCharacter.changeLevel (dvd_mul_right M k) l *
        DirichletCharacter.changeLevel (dvd_mul_left k M) χ) t ht'
    refine le_of_eq_of_le ?_ hcb'
    congr 2
    apply Finset.sum_congr rfl; intro m _
    rw [changeLevel_mul_apply]
    simp only [coefN]; ring
  obtain ⟨K₀, hK₀⟩ := marked_type_ii_of_coefficient_bound δ 1 18 (1 / 2) hδ one_pos
    (by norm_num) (by norm_num) (by norm_num) c₁ c₂ hc₁ S hS hα
  refine ⟨K₀, fun K hK1 hK a ha hab => ?_⟩
  obtain ⟨A₁, x₁, hmain⟩ := hK₀ K hK1 hK a ha hab
  have hV : ∀ᶠ x in atTop, ∀ i, 1 / 2 ≤ groupReciprocalSum x (a i) :=
    Filter.eventually_all.mpr fun i =>
      eventually_groupReciprocalSum (a i) (by linarith [(hab i).1])
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp hV
  refine ⟨9 * (Fintype.card (DirichletCharacter ℂ M) : ℝ) * max A₁ 0 +
        9 * ((1 + Cα) * (Lip * (4 * c₂)) * 2 ^ K), max (max x₁ X) X₂, ?_⟩
  intro x hx Hm Hn h1 h2 h3 h4 J hJ hJs hs1 hs2 b hb1' hb1
  have hxX : X ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hxx₁ : x₁ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hxV := hX₂ x (le_trans (le_max_right _ _) hx)
  obtain ⟨hx1, hL1, hLc, hLM, hCL, hW, hxδ2⟩ := hXfacts x hxX
  have hHm : 2 ≤ Hm := le_trans hxδ2 h1
  have hHn : 2 ≤ Hn := le_trans hxδ2 h2
  refine core M c u hM hu Ψ hΨ0 hΨ1 Lip hLip γ sMinus sPlus Cα c₁ c₂ hγs hsPlus hCα0 hc₁ a A₁
    x Hm Hn J b (hX x hxX).1 hxV hx1 hL1 hW hHm hHn h3 h4 hJs hs1 hs2 hb1' hb1 ?_
  intro l i j
  have hmem : (x, Hm, Hn, (fun m : ℕ => coefN γ x (cell J Hm ⌈log x ^ (6 : ℝ)⌉₊ i) 0 m * l (m : ZMod M)),
      (fun n : ℕ => if idx Hn ⌈log x ^ (6 : ℝ)⌉₊ n = j then b n * l (n : ZMod M) else 0)) ∈ S := by
    refine ⟨hxX, h1, h2, h3, h4, hs1, hs2,
      ⟨cell J Hm _ i, cell_ordConnected hJ (by linarith) _ i, fun y hy => hJs hy.1, l, rfl⟩,
      fun n hn => ?_, fun n => ?_⟩
    · apply hb1 n; intro h0; apply hn; simp [h0]
    · dsimp only
      rw [Real.rpow_one]
      split_ifs
      · rw [norm_mul]
        calc ‖b n‖ * ‖l (n : ZMod M)‖ ≤ 1 * 1 :=
              mul_le_mul (hb1' n) (DirichletCharacter.norm_le_one _ _) (norm_nonneg _)
                zero_le_one
          _ ≤ log x := by linarith
      · rw [norm_zero]; linarith
  have hF1 : ∀ h, 0 < h → ‖(predecessorIndicator x a c h : ℂ)‖ ≤ 1 := by
    intro h _
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (predecessorIndicator_nonneg _ _ _ _)]
    exact predecessorIndicator_le_one _ _ _ _
  have hF2 : ∀ h, 0 < h → ∀ p ∈ groupPrimes x a,
      (predecessorIndicator x a c (p * h) : ℂ) = predecessorIndicator x a c h := by
    intro h hh p hp; rw [predecessorIndicator_mul x a c h hh p hp]
  exact hmain x Hm Hn _ _ hmem hxx₁ (fun h => (predecessorIndicator x a c h : ℂ)) hF1 hF2
