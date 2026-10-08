-- Prove2me | solution 1 for ArtinPrimitiveRoots.balanced_cost
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:20:16.629918+00:00
-- url     : https://prove2.me/submissions/0321e699-e5a0-4a68-b302-972b828b2897
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_harmonic_mass
import Theorems.Thm_ArtinPrimitiveRoots_mertens_product
import Theorems.Thm_ArtinPrimitiveRoots_rough_pairs_upper_bound
import Theorems.Thm_ArtinPrimitiveRoots_type_ii_progression
import Theorems.Thm_ArtinPrimitiveRoots_weighted_family_distribution

namespace ArtinPrimitiveRoots.P21balanced_cost

open Real Filter Topology MeasureTheory

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

lemma predecessorIndicator_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (c h : ℕ) :
    0 ≤ predecessorIndicator x a c h := by
  unfold predecessorIndicator; split_ifs <;> norm_num

lemma constructionWeight_nonneg (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ)
    {K : ℕ} (a : Fin K → ℝ) (d : ℕ) : 0 ≤ constructionWeight M c u Ψ x a d := by
  unfold constructionWeight
  split_ifs
  · exact mul_nonneg (mul_nonneg (hΨ0 _) (predecessorIndicator_nonneg _ _ _ _))
      (mark_nonneg _ _ _)
  · exact le_rfl

lemma constructionWeight_support (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ)
    (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2) (x : ℝ) (hx : 0 < x) {K : ℕ} (a : Fin K → ℝ) (d : ℕ)
    (hd : constructionWeight M c u Ψ x a d ≠ 0) :
    2 ≤ d ∧ (d : ℤ) ≡ u [ZMOD M] ∧ x < d ∧ (d : ℝ) < 2 * x ∧
      ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ (d - 1) / groupPart x a (d - 1) = c * Q := by
  unfold constructionWeight at hd
  split_ifs at hd with h
  · refine ⟨h.1, h.2, ?_⟩
    have hΨ : Ψ (d / x) ≠ 0 := fun e => hd (by rw [e]; ring)
    have hF : predecessorIndicator x a c (d - 1) ≠ 0 := fun e => hd (by rw [e]; ring)
    have hmem := hΨs (subset_tsupport _ hΨ)
    rw [Set.mem_Ioo, lt_div_iff₀ hx, div_lt_iff₀ hx] at hmem
    refine ⟨by linarith [hmem.1], by linarith [hmem.2], ?_⟩
    unfold predecessorIndicator at hF
    split_ifs at hF with hQ
    · exact hQ
    · exact absurd rfl hF
  · exact absurd rfl hd

lemma weight_eq_zero_of_ge (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (x : ℝ) (hx : 0 < x) {K : ℕ} (a : Fin K → ℝ) (d : ℕ) (hd : ⌈2 * x⌉₊ ≤ d) :
    constructionWeight M c u Ψ x a d = 0 := by
  by_contra hne
  have := (constructionWeight_support M c u Ψ hΨs x hx a d hne).2.2.2.1
  have h2 : (⌈2 * x⌉₊ : ℝ) ≤ d := by exact_mod_cast hd
  have h3 := Nat.le_ceil (2 * x)
  linarith

lemma tsum_weight_eq_sum (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (x : ℝ) (hx : 0 < x) {K : ℕ} (a : Fin K → ℝ) (P : ℕ → Prop) [DecidablePred P] :
    ∑' d : ℕ, (if P d then constructionWeight M c u Ψ x a d else 0) =
      ∑ d ∈ Finset.range ⌈2 * x⌉₊, (if P d then constructionWeight M c u Ψ x a d else 0) := by
  apply tsum_eq_sum
  intro d hd
  simp only [Finset.mem_range, not_lt] at hd
  rw [weight_eq_zero_of_ge M c u Ψ hΨs x hx a d hd]
  simp

lemma totalMass_nonneg (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ) {K : ℕ}
    (a : Fin K → ℝ) : 0 ≤ totalMass M c u Ψ x a :=
  tsum_nonneg fun d => constructionWeight_nonneg M c u Ψ hΨ0 x a d

/-- The integration region of `D_{γ,j}` with `n = j - 1` variables. -/
def regionD (n : ℕ) (γ w : ℝ) : Set (Fin n → ℝ) :=
  {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ}

/-- The integrand of `D_{γ,j}`. -/
noncomputable def integrandD (n : ℕ) (w : ℝ) (t : Fin n → ℝ) : ℝ :=
  (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹

lemma regionD_empty (n : ℕ) (γ w : ℝ) (h : w < (n + 1) * γ) : regionD n γ w = ∅ := by
  ext t
  simp only [regionD, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
  intro ht
  have : ∑ _i : Fin n, γ ≤ ∑ i, t i := Finset.sum_le_sum fun i _ => ht i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  linarith

lemma roughDensityTerm_succ_succ (γ w : ℝ) (j : ℕ) :
    roughDensityTerm γ w (j + 2) =
      (1 / ((j + 2).factorial : ℝ)) * ∫ t in regionD (j + 1) γ w, integrandD (j + 1) w t := rfl

lemma roughDensityTerm_nonneg (γ w : ℝ) (hγ : 0 < γ) (hw : 0 < w) (j : ℕ) :
    0 ≤ roughDensityTerm γ w j := by
  match j with
  | 0 => simp [roughDensityTerm]
  | 1 => simp only [roughDensityTerm]; positivity
  | j + 2 =>
    simp only [roughDensityTerm]
    apply mul_nonneg (by positivity)
    have hclosed : IsClosed {t : Fin (j + 1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ} := by
      rw [Set.setOf_and, Set.ofPred_forall]
      exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
        (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
    apply setIntegral_nonneg hclosed.measurableSet
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    apply mul_nonneg
    · apply inv_nonneg.mpr; linarith
    · apply Finset.prod_nonneg
      intro i _
      exact inv_nonneg.mpr (le_trans hγ.le (h1 i))

lemma roughDensity_nonneg (γ w : ℝ) (hγ : 0 < γ) (hw : 0 < w) : 0 ≤ roughDensity γ w :=
  tsum_nonneg fun j => roughDensityTerm_nonneg γ w hγ hw j

lemma floor_two_mul_pow (l : ℕ) : ⌊(2 : ℝ) * 2 ^ l⌋₊ = 2 ^ (l + 1) := by
  rw [show (2 : ℝ) * 2 ^ l = ((2 ^ (l + 1) : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]

lemma filter_Ico_eq (l : ℕ)
    [DecidablePred (fun m : ℕ => (m : ℝ) ∈ Set.Ico ((2 : ℝ) ^ l) (2 ^ (l + 1)))] :
    (Finset.range (⌊(2 : ℝ) * 2 ^ l⌋₊ + 1)).filter
        (fun m : ℕ => (m : ℝ) ∈ Set.Ico ((2 : ℝ) ^ l) (2 ^ (l + 1))) =
      Finset.Ico (2 ^ l) (2 ^ (l + 1)) := by
  rw [floor_two_mul_pow]
  ext m
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ico, Finset.mem_Ico]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, by exact_mod_cast h1, by exact_mod_cast h2⟩

open Classical in
/-- One dyadic block of the Type II estimate in the progression (Lemma 12.1), in real form. -/
lemma typeII_block (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (x : ℝ) {K : ℕ} (a : Fin K → ℝ)
    (γ A δ sMinus sPlus : ℝ)
    (hT : ∀ Hm Hn : ℝ, x ^ δ ≤ Hm → x ^ δ ≤ Hn → 1 / 4 * x ≤ Hm * Hn → Hm * Hn ≤ 2 * x →
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc Hm (2 * Hm) →
      sMinus ≤ log Hm / log x → log (2 * Hm) / log x ≤ sPlus →
      ∀ b : ℕ → ℂ, (∀ n, ‖b n‖ ≤ 1) →
        (∀ n, b n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
      ‖∑ m ∈ (Finset.range (⌊2 * Hm⌋₊ + 1)).filter (fun m : ℕ => (m : ℝ) ∈ J),
          ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
          ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) * b n *
            (constructionWeight M c u Ψ x a (m * n) : ℂ)‖ ≤ A * (Hm * Hn) * log x ^ (-6 : ℝ))
    (k l : ℕ) (β : ℕ → ℝ) (hβ1 : ∀ n, |β n| ≤ 1)
    (hβr : ∀ n, β n ≠ 0 → IsRough (sieveLevel x) n)
    (h1 : x ^ δ ≤ 2 ^ l) (h2 : x ^ δ ≤ 2 ^ k) (h3 : 1 / 4 * x ≤ 2 ^ l * 2 ^ k)
    (h4 : (2 : ℝ) ^ l * 2 ^ k ≤ 2 * x) (h5 : sMinus ≤ log (2 ^ l) / log x)
    (h6 : log (2 * 2 ^ l) / log x ≤ sPlus) :
    |∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        (roughIndicator x γ m - roughProxy x γ m) * β n *
          constructionWeight M c u Ψ x a (m * n)| ≤
      A * (2 ^ l * 2 ^ k) * log x ^ (-6 : ℝ) := by
  classical
  set b : ℕ → ℂ := fun n => if n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)) then (β n : ℂ) else 0
    with hb
  have hJ : (Set.Ico ((2 : ℝ) ^ l) (2 ^ (l + 1))).OrdConnected := Set.ordConnected_Ico
  have hJsub : Set.Ico ((2 : ℝ) ^ l) (2 ^ (l + 1)) ⊆ Set.Icc (2 ^ l) (2 * 2 ^ l) := by
    intro y hy; exact ⟨hy.1, by rw [pow_succ] at hy; linarith [hy.2]⟩
  have hb1 : ∀ n, ‖b n‖ ≤ 1 := by
    intro n; simp only [hb]; split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs]; exact hβ1 n
    · simp
  have hbs : ∀ n, b n ≠ 0 → (2 : ℝ) ^ k ≤ n ∧ (n : ℝ) ≤ 2 * 2 ^ k ∧
      IsRough (sieveLevel x) n := by
    intro n hn
    simp only [hb] at hn
    split_ifs at hn with hmem
    · rw [Finset.mem_Ico] at hmem
      refine ⟨by exact_mod_cast hmem.1, ?_, hβr n (fun e => hn (by rw [e]; simp))⟩
      have : (n : ℝ) < 2 ^ (k + 1) := by exact_mod_cast hmem.2
      rw [pow_succ] at this; linarith
    · exact absurd rfl hn
  have key := hT (2 ^ l) (2 ^ k) h1 h2 h3 h4 _ hJ hJsub h5 h6 b hb1 hbs
  rw [filter_Ico_eq] at key
  have hsum : ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.range (⌊2 * (2 : ℝ) ^ k⌋₊ + 1),
      ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) * b n *
        (constructionWeight M c u Ψ x a (m * n) : ℂ) =
      ((∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        (roughIndicator x γ m - roughProxy x γ m) * β n *
          constructionWeight M c u Ψ x a (m * n) : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro m _
    rw [floor_two_mul_pow]
    have hsub : Finset.Ico (2 ^ k) (2 ^ (k + 1)) ⊆ Finset.range (2 ^ (k + 1) + 1) := by
      intro n hn; rw [Finset.mem_Ico] at hn; rw [Finset.mem_range]; omega
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro n hn
      simp only [hb, if_pos hn]
    · intro n _ hn
      simp only [hb, if_neg hn]; ring
  rw [hsum, Complex.norm_real, Real.norm_eq_abs] at key
  exact key

lemma mertensProduct_pos (y : ℝ) : 0 < mertensProduct y := by
  unfold mertensProduct
  apply Finset.prod_pos
  intro p hp
  simp only [Finset.mem_filter] at hp
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
  have : 1 / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

lemma isRough_of_prime (y : ℝ) (n : ℕ) (hn : n.Prime) (hyn : y < n) : IsRough y n :=
  ⟨hn.pos, fun p hp => by rw [hn.primeFactors, Finset.mem_singleton] at hp; rw [hp]; exact hyn⟩

lemma eventually_sieveLevel_lt (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, sieveLevel x < x ^ γ := by
  have h1 : Tendsto (fun x : ℝ => log x ^ (-(0.76 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp Real.tendsto_log_atTop
  filter_upwards [h1.eventually (gt_mem_nhds hγ), Real.tendsto_log_atTop.eventually_gt_atTop 0,
    eventually_gt_atTop 0] with x hx hL hx0
  unfold sieveLevel
  rw [Real.rpow_def_of_pos hx0, Real.exp_lt_exp]
  have : log x ^ (0.24 : ℝ) = log x ^ (-(0.76 : ℝ)) * log x := by
    rw [← Real.rpow_add_one hL.ne']; norm_num
  rw [this, mul_comm (log x) γ]
  exact mul_lt_mul_of_pos_right hx hL

lemma rpow_neg_six (L : ℝ) (hL : 0 < L) : L ^ (-6 : ℝ) = 1 / L ^ 6 := by
  rw [Real.rpow_neg hL.le, one_div]
  congr 1
  exact_mod_cast Real.rpow_natCast L 6

/-- The error bound `L_m^2 · A⁺ · 2x · L^{-6} ≤ η 𝔖 X₀ / L`. -/
lemma typeII_error_small (x L A' Lm η S c₁ X J : ℝ) (hL : 1 ≤ L) (hx : 0 < x) (hA' : 0 ≤ A')
    (hLm0 : 0 ≤ Lm) (hLm : Lm ≤ 2 * L) (hη : 0 < η) (hS : 0 < S) (hc₁ : 0 < c₁)
    (hJ : 1 ≤ J) (hX : c₁ * (x * J / L) ≤ X) (hLbig : 8 * A' / (η * S * c₁) ≤ L) :
    Lm ^ 2 * (A' * (2 * x) * L ^ (-6 : ℝ)) ≤ η * (S * X / L) := by
  have hL0 : 0 < L := by linarith
  rw [rpow_neg_six L hL0]
  have h1 : Lm ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  have hXlow : c₁ * x / L ≤ X := by
    refine le_trans ?_ hX
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hc₁.le
    apply div_le_div_of_nonneg_right _ hL0.le
    nlinarith
  have hkey : 8 * A' ≤ η * S * c₁ * L ^ 2 := by
    have hpos : 0 < η * S * c₁ := by positivity
    rw [div_le_iff₀ hpos] at hLbig
    nlinarith
  calc Lm ^ 2 * (A' * (2 * x) * (1 / L ^ 6))
      ≤ 4 * L ^ 2 * (A' * (2 * x) * (1 / L ^ 6)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 8 * A' * (x / L ^ 4) := by field_simp; ring
    _ ≤ η * S * c₁ * L ^ 2 * (x / L ^ 4) := mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = η * S * (c₁ * x / L) / L := by field_simp
    _ ≤ η * S * X / L := by
        apply div_le_div_of_nonneg_right _ hL0.le
        exact mul_le_mul_of_nonneg_left hXlow (by positivity)
    _ = η * (S * X / L) := by ring

/-- `D_{0.4}(s) = 1/s` for `0 < s < 0.8`. -/
lemma roughDensity_four (s : ℝ) (hs : s < 0.8) : roughDensity 0.4 s = 1 / s := by
  unfold roughDensity
  rw [tsum_eq_single 1]
  · rfl
  · intro j hj
    match j, hj with
    | 0, _ => rfl
    | k + 2, _ =>
      rw [roughDensityTerm_succ_succ, regionD_empty, MeasureTheory.Measure.restrict_empty,
        MeasureTheory.integral_zero_measure, mul_zero]
      push_cast
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith

lemma isRough_mono {y y' : ℝ} (h : y ≤ y') {m : ℕ} (hm : IsRough y' m) : IsRough y m :=
  ⟨hm.1, fun p hp => lt_of_le_of_lt h (hm.2 p hp)⟩

lemma eventually_mertens_lower :
    ∀ᶠ x : ℝ in atTop, 1 ≤ 0.46 * log x * mertensProduct (sieveLevel x) := by
  have hγ : (1 : ℝ) / 4 < exp (-eulerMascheroniConstant) := by
    have h1 : exp (-(2 / 3 : ℝ)) < exp (-eulerMascheroniConstant) :=
      Real.exp_lt_exp.mpr (by linarith [eulerMascheroniConstant_lt_two_thirds])
    have h2 : (1 : ℝ) / 4 < exp (-(2 / 3 : ℝ)) := by
      rw [← Real.log_lt_iff_lt_exp (by norm_num)]
      have : log (1 / 4 : ℝ) = -(2 * log 2) := by
        rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      rw [this]; linarith [Real.log_two_gt_d9]
    linarith
  have hW : Tendsto (fun x : ℝ => sieveLevel x) atTop atTop := by
    unfold sieveLevel
    exact Real.tendsto_exp_atTop.comp
      ((tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop)
  have h1 := (mertens_product.comp hW).eventually (lt_mem_nhds hγ)
  have h2 : Tendsto (fun x : ℝ => log x ^ (0.76 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  filter_upwards [h1, h2.eventually_ge_atTop 9, Real.tendsto_log_atTop.eventually_gt_atTop 0]
    with x hx hx2 hL
  simp only [Function.comp] at hx
  have hlogW : log (sieveLevel x) = log x ^ (0.24 : ℝ) := by
    unfold sieveLevel; rw [Real.log_exp]
  rw [hlogW] at hx
  have hV := mertensProduct_pos (sieveLevel x)
  have hsplit : log x = log x ^ (0.76 : ℝ) * log x ^ (0.24 : ℝ) := by
    rw [← Real.rpow_add hL]; norm_num
  rw [hsplit]
  have : 0 < log x ^ (0.24 : ℝ) := Real.rpow_pos_of_pos hL _
  nlinarith

/-- At most three `k` have `x/4 < 2^l 2^k < 2x`. -/
lemma card_relevant_le (x : ℝ) (hx : 0 < x) (l : ℕ) (S : Finset ℕ) :
    (S.filter (fun k : ℕ => x / 4 < (2 : ℝ) ^ l * 2 ^ k ∧ (2 : ℝ) ^ l * 2 ^ k < 2 * x)).card
      ≤ 3 := by
  set T := S.filter (fun k : ℕ => x / 4 < (2 : ℝ) ^ l * 2 ^ k ∧ (2 : ℝ) ^ l * 2 ^ k < 2 * x)
  rcases T.eq_empty_or_nonempty with h | h
  · rw [h]; simp
  set k₀ := T.min' h
  have hk₀ : k₀ ∈ T := T.min'_mem h
  have hsub : T ⊆ Finset.Ico k₀ (k₀ + 3) := by
    intro k hk
    rw [Finset.mem_Ico]
    refine ⟨T.min'_le k hk, ?_⟩
    simp only [T, Finset.mem_filter] at hk hk₀
    have h1 : (2 : ℝ) ^ l * 2 ^ k < 8 * ((2 : ℝ) ^ l * 2 ^ k₀) := by linarith [hk.2.2, hk₀.2.1]
    have h2 : (2 : ℝ) ^ k < 2 ^ (k₀ + 3) := by
      rw [pow_add]
      have : (0 : ℝ) < 2 ^ l := by positivity
      nlinarith
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h2
    omega
  calc T.card ≤ (Finset.Ico k₀ (k₀ + 3)).card := Finset.card_le_card hsub
    _ = 3 := by simp

/-- The number of dyadic scales meeting `(x^{1/2-κ}, 2x^{1/2+κ})` is at most `3 + 3κL`. -/
lemma card_scales_le (x κ : ℝ) (hx : 1 < x) (hκ : 0 < κ) (S : Finset ℕ) :
    ((S.filter (fun l : ℕ => x ^ (1 / 2 - κ) < (2 : ℝ) ^ (l + 1) ∧
      (2 : ℝ) ^ l < 2 * x ^ (1 / 2 + κ))).card : ℝ) ≤ 3 + 3 * κ * log x := by
  set T := S.filter (fun l : ℕ => x ^ (1 / 2 - κ) < (2 : ℝ) ^ (l + 1) ∧
      (2 : ℝ) ^ l < 2 * x ^ (1 / 2 + κ))
  have hx0 : 0 < x := by linarith
  have hL : 0 < log x := Real.log_pos hx
  have hl2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hl2' : 2 / 3 < log 2 := by linarith [Real.log_two_gt_d9]
  rcases T.eq_empty_or_nonempty with h | h
  · rw [h]; simp; positivity
  set l₁ := T.min' h
  have hl₁ : l₁ ∈ T := T.min'_mem h
  set B : ℝ := 2 + 2 * κ * log x / log 2
  have hsub : T ⊆ Finset.Ico l₁ (l₁ + ⌈B⌉₊) := by
    intro l hl
    rw [Finset.mem_Ico]
    refine ⟨T.min'_le l hl, ?_⟩
    simp only [T, Finset.mem_filter] at hl hl₁
    have h1 : (l : ℝ) * log 2 < log 2 + (1 / 2 + κ) * log x := by
      have := Real.log_lt_log (by positivity) hl.2.2
      rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at this
      linarith
    have h2 : (1 / 2 - κ) * log x < ((l₁ : ℝ) + 1) * log 2 := by
      have := Real.log_lt_log (by positivity) hl₁.2.1
      rw [Real.log_pow, Real.log_rpow hx0] at this
      push_cast at this
      linarith
    have h3 : (l : ℝ) < l₁ + B := by
      have : ((l : ℝ) - l₁) * log 2 < 2 * log 2 + 2 * κ * log x := by nlinarith
      have h4 : (l : ℝ) - l₁ < (2 * log 2 + 2 * κ * log x) / log 2 := by
        rw [lt_div_iff₀ hl2]; exact this
      have : (2 * log 2 + 2 * κ * log x) / log 2 = B := by
        simp only [B]; field_simp
      linarith
    have h5 : (l : ℝ) < l₁ + ⌈B⌉₊ := lt_of_lt_of_le h3 (by linarith [Nat.le_ceil B])
    exact_mod_cast h5
  have hB0 : 0 ≤ B := by positivity
  calc (T.card : ℝ) ≤ (Finset.Ico l₁ (l₁ + ⌈B⌉₊)).card := by exact_mod_cast Finset.card_le_card hsub
    _ = ⌈B⌉₊ := by simp
    _ ≤ B + 1 := (Nat.ceil_lt_add_one hB0).le
    _ ≤ 3 + 3 * κ * log x := by
        simp only [B]
        have : 2 * κ * log x / log 2 ≤ 3 * κ * log x := by
          rw [div_le_iff₀ hl2]
          have : 0 ≤ κ * log x := by positivity
          nlinarith
        linarith

/-- Grouping a sum by dyadic scale. -/
lemma sum_le_sum_scales (g : ℕ → ℝ) (hg : ∀ m, 0 ≤ g m) (Mset Lset : Finset ℕ)
    (hM : ∀ m ∈ Mset, 1 ≤ m ∧ Nat.log 2 m ∈ Lset) :
    ∑ m ∈ Mset, g m ≤ ∑ l ∈ Lset, ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), g m := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Nat.log 2) (fun m hm => (hM m hm).2)]
  apply Finset.sum_le_sum
  intro l _
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmM, hml⟩ := hm
    have h1 := (hM m hmM).1
    rw [Finset.mem_Ico]
    constructor
    · rw [← hml]; exact Nat.pow_log_le_self 2 (by omega)
    · rw [← hml]; exact Nat.lt_pow_succ_log_self (by norm_num) m
  · intro m _ _; exact hg m

lemma filter_box_eq (y : ℝ) (l : ℕ)
    [DecidablePred (fun m : ℕ => (2 : ℝ) ^ l ≤ m ∧ (m : ℝ) < 2 * 2 ^ l ∧ IsRough y m)]
    [DecidablePred (fun m : ℕ => IsRough y m)] :
    (Finset.range ⌈2 * (2 : ℝ) ^ l⌉₊).filter
        (fun m : ℕ => (2 : ℝ) ^ l ≤ m ∧ (m : ℝ) < 2 * 2 ^ l ∧ IsRough y m) =
      (Finset.Ico (2 ^ l) (2 ^ (l + 1))).filter (fun m => IsRough y m) := by
  have hc : ⌈2 * (2 : ℝ) ^ l⌉₊ = 2 ^ (l + 1) := by
    rw [show (2 : ℝ) * 2 ^ l = ((2 ^ (l + 1) : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]
  rw [hc]
  ext m
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨-, h1, h2, h3⟩
    refine ⟨⟨by exact_mod_cast h1, ?_⟩, h3⟩
    have : (m : ℝ) < 2 ^ (l + 1) := by rw [pow_succ]; linarith
    exact_mod_cast this
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h2, by exact_mod_cast h1, ?_, h3⟩
    have : (m : ℝ) < 2 ^ (l + 1) := by exact_mod_cast h2
    rw [pow_succ] at this; linarith

open Classical in
lemma roughProxy_four_le (x : ℝ) (hx : 1 < x) (m : ℕ) (hm1 : x ^ (0.46 : ℝ) ≤ m)
    (hm2 : (m : ℝ) < x ^ (0.54 : ℝ)) :
    roughProxy x 0.4 m ≤ 1 / (0.46 * log x * mertensProduct (sieveLevel x)) *
      (if IsRough (sieveLevel x) m then 1 else 0) := by
  classical
  have hx0 : 0 < x := by linarith
  have hL : 0 < log x := Real.log_pos hx
  have hV := mertensProduct_pos (sieveLevel x)
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm1
  have hs1 : 0.46 ≤ log m / log x := by
    rw [le_div_iff₀ hL]
    have := Real.log_le_log (by positivity) hm1
    rwa [Real.log_rpow hx0] at this
  have hs2 : log m / log x < 0.8 := by
    rw [div_lt_iff₀ hL]
    have := Real.log_lt_log hm0 hm2
    rw [Real.log_rpow hx0] at this
    nlinarith
  unfold roughProxy
  rw [roughDensity_four _ hs2]
  apply mul_le_mul_of_nonneg_right _ (by split_ifs <;> norm_num)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rw [one_div_mul_eq_div, div_le_iff₀ (by linarith)]
  have : 0 < log x * mertensProduct (sieveLevel x) := by positivity
  nlinarith

lemma roughProxy_nonneg (x γ : ℝ) (hx : 1 < x) (hγ : 0 < γ) (m : ℕ) :
    0 ≤ roughProxy x γ m := by
  classical
  have hL : 0 < log x := Real.log_pos hx
  have hV := mertensProduct_pos (sieveLevel x)
  unfold roughProxy
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; simp only [Nat.cast_zero, Real.log_zero, zero_div]
    apply mul_nonneg _ (by split_ifs <;> norm_num)
    apply div_nonneg _ (by positivity)
    unfold roughDensity
    apply tsum_nonneg
    intro j
    match j with
    | 0 => simp [roughDensityTerm]
    | 1 => simp [roughDensityTerm]
    | k + 2 =>
      rw [roughDensityTerm_succ_succ, regionD_empty, MeasureTheory.Measure.restrict_empty,
        MeasureTheory.integral_zero_measure, mul_zero]
      push_cast; nlinarith
  · have hm : (1 : ℝ) ≤ m := by exact_mod_cast h0
    rcases eq_or_lt_of_le hm with h1 | h1
    · rw [← h1]; simp only [Real.log_one, zero_div]
      apply mul_nonneg _ (by split_ifs <;> norm_num)
      apply div_nonneg _ (by positivity)
      unfold roughDensity
      apply tsum_nonneg
      intro j
      match j with
      | 0 => simp [roughDensityTerm]
      | 1 => simp [roughDensityTerm]
      | k + 2 =>
        rw [roughDensityTerm_succ_succ, regionD_empty, MeasureTheory.Measure.restrict_empty,
          MeasureTheory.integral_zero_measure, mul_zero]
        push_cast; nlinarith
    · apply mul_nonneg _ (by split_ifs <;> norm_num)
      apply div_nonneg _ (by positivity)
      exact roughDensity_nonneg γ _ hγ (div_pos (Real.log_pos h1) hL)

open Classical in
/-- The bound for one balanced box (§12.5): two Type II replacements and Lemma 12.5. -/
lemma box_bound (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨ0 : ∀ y, 0 ≤ Ψ y)
    (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A C₁ : ℝ) (hx : 1 < x)
    (hT : ∀ Hm Hn : ℝ, x ^ (0.4 : ℝ) ≤ Hm → x ^ (0.4 : ℝ) ≤ Hn → 1 / 4 * x ≤ Hm * Hn →
      Hm * Hn ≤ 2 * x →
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc Hm (2 * Hm) →
      0.46 ≤ log Hm / log x → log (2 * Hm) / log x ≤ 0.54 →
      ∀ β : ℕ → ℂ, (∀ n, ‖β n‖ ≤ 1) →
        (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
      ‖∑ m ∈ (Finset.range (⌊2 * Hm⌋₊ + 1)).filter (fun m : ℕ => (m : ℝ) ∈ J),
          ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
          ((roughIndicator x 0.4 m - roughProxy x 0.4 m : ℝ) : ℂ) * β n *
            (constructionWeight M c u Ψ x a (m * n) : ℂ)‖ ≤ A * (Hm * Hn) * log x ^ (-6 : ℝ))
    (hRP : ∀ M₁ M₂ : ℝ, x / 4 ≤ M₁ * M₂ → M₁ * M₂ ≤ 2 * x →
        x ^ (0.46 : ℝ) / 2 ≤ M₁ → M₁ ≤ 2 * x ^ (0.54 : ℝ) →
        x ^ (0.46 : ℝ) / 2 ≤ M₂ → M₂ ≤ 2 * x ^ (0.54 : ℝ) →
        ∑ m ∈ (Finset.range ⌈2 * M₁⌉₊).filter
              (fun m : ℕ => M₁ ≤ m ∧ (m : ℝ) < 2 * M₁ ∧ IsRough (sieveLevel x) m),
          ∑ n ∈ (Finset.range ⌈2 * M₂⌉₊).filter
              (fun n : ℕ => M₂ ≤ n ∧ (n : ℝ) < 2 * M₂ ∧ IsRough (sieveLevel x) n),
            constructionWeight M c u Ψ x a (m * n) ≤
          C₁ * totalMass M c u Ψ x a * mertensProduct (sieveLevel x) ^ 2)
    (hV : 1 ≤ 0.46 * log x * mertensProduct (sieveLevel x))
    (hW : sieveLevel x ≤ x ^ (0.4 : ℝ))
    (l k : ℕ) (hl1 : x ^ (0.46 : ℝ) ≤ 2 ^ l) (hl2 : 2 * (2 : ℝ) ^ l ≤ x ^ (0.54 : ℝ))
    (hk1 : x ^ (0.46 : ℝ) ≤ 2 ^ k) (hk2 : 2 * (2 : ℝ) ^ k ≤ x ^ (0.54 : ℝ))
    (h3 : x / 4 < (2 : ℝ) ^ l * 2 ^ k) (h4 : (2 : ℝ) ^ l * 2 ^ k < 2 * x) :
    ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        roughIndicator x 0.4 m * roughIndicator x 0.4 n * constructionWeight M c u Ψ x a (m * n)
      ≤ max C₁ 0 * totalMass M c u Ψ x a / (0.46 * log x) ^ 2 +
        2 * (max A 0 * (2 * x) * log x ^ (-6 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < log x := Real.log_pos hx
  have hL6 : 0 ≤ log x ^ (-6 : ℝ) := Real.rpow_nonneg hL.le _
  have hVpos := mertensProduct_pos (sieveLevel x)
  set V := mertensProduct (sieveLevel x) with hVdef
  set R := roughIndicator x 0.4 with hR
  set B := roughProxy x 0.4 with hB
  set w := constructionWeight M c u Ψ x a with hw
  set X₀ := totalMass M c u Ψ x a with hX₀
  have hX0 : 0 ≤ X₀ := totalMass_nonneg M c u Ψ hΨ0 x a
  have hw0 : ∀ d, 0 ≤ w d := constructionWeight_nonneg M c u Ψ hΨ0 x a
  have hR1 : ∀ n, |R n| ≤ 1 := fun n => by
    simp only [hR, roughIndicator]; split_ifs <;> norm_num
  have hRr : ∀ n, R n ≠ 0 → IsRough (sieveLevel x) n := by
    intro n hn
    simp only [hR, roughIndicator] at hn
    split_ifs at hn with h
    · exact isRough_mono hW h
    · exact absurd rfl hn
  -- the scale conditions
  have hpow4 : x ^ (0.4 : ℝ) ≤ x ^ (0.46 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
  have hlog46 : ∀ j : ℕ, x ^ (0.46 : ℝ) ≤ 2 ^ j → 0.46 ≤ log (2 ^ j) / log x := by
    intro j hj
    rw [le_div_iff₀ hL]
    have := Real.log_le_log (by positivity) hj
    rwa [Real.log_rpow hx0] at this
  have hlog54 : ∀ j : ℕ, 2 * (2 : ℝ) ^ j ≤ x ^ (0.54 : ℝ) →
      log (2 * 2 ^ j) / log x ≤ 0.54 := by
    intro j hj
    rw [div_le_iff₀ hL]
    have := Real.log_le_log (by positivity) hj
    rwa [Real.log_rpow hx0] at this
  have h3' : 1 / 4 * x ≤ (2 : ℝ) ^ l * 2 ^ k := by linarith
  have h3'' : 1 / 4 * x ≤ (2 : ℝ) ^ k * 2 ^ l := by linarith
  have h4' : (2 : ℝ) ^ k * 2 ^ l ≤ 2 * x := by linarith
  -- first Type II application
  have hE₁ := typeII_block M c u Ψ x a 0.4 A 0.4 0.46 0.54 hT k l R hR1 hRr
    (le_trans hpow4 hl1) (le_trans hpow4 hk1) h3' h4.le (hlog46 l hl1) (hlog54 l hl2)
  -- second Type II application
  set β : ℕ → ℝ := fun m => if m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)) then B m else 0 with hβ
  have hboxm : ∀ m : ℕ, m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)) → x ^ (0.46 : ℝ) ≤ m ∧
      (m : ℝ) < x ^ (0.54 : ℝ) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have h1 : (2 : ℝ) ^ l ≤ m := by exact_mod_cast hm.1
    have h2 : (m : ℝ) < 2 ^ (l + 1) := by exact_mod_cast hm.2
    rw [pow_succ] at h2
    constructor <;> linarith
  have hboxn : ∀ n : ℕ, n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)) → x ^ (0.46 : ℝ) ≤ n ∧
      (n : ℝ) < x ^ (0.54 : ℝ) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have h1 : (2 : ℝ) ^ k ≤ n := by exact_mod_cast hn.1
    have h2 : (n : ℝ) < 2 ^ (k + 1) := by exact_mod_cast hn.2
    rw [pow_succ] at h2
    constructor <;> linarith
  have hBle : ∀ m : ℕ, x ^ (0.46 : ℝ) ≤ m → (m : ℝ) < x ^ (0.54 : ℝ) →
      B m ≤ 1 / (0.46 * log x * V) * (if IsRough (sieveLevel x) m then 1 else 0) :=
    fun m h1 h2 => roughProxy_four_le x hx m h1 h2
  have hB0 : ∀ m, 0 ≤ B m := fun m => roughProxy_nonneg x 0.4 hx (by norm_num) m
  have hβ1 : ∀ m, |β m| ≤ 1 := by
    intro m
    simp only [hβ]
    split_ifs with hm
    · rw [abs_of_nonneg (hB0 m)]
      obtain ⟨h1, h2⟩ := hboxm m hm
      refine le_trans (hBle m h1 h2) ?_
      have : 1 / (0.46 * log x * V) ≤ 1 := by
        rw [div_le_one (by positivity)]; exact hV
      split_ifs <;> linarith
    · simp
  have hβr : ∀ m, β m ≠ 0 → IsRough (sieveLevel x) m := by
    intro m hm
    simp only [hβ] at hm
    split_ifs at hm with hm'
    · by_contra hr
      apply hm
      simp only [hB, roughProxy, if_neg hr, mul_zero]
    · exact absurd rfl hm
  have hE₂ := typeII_block M c u Ψ x a 0.4 A 0.4 0.46 0.54 hT l k β hβ1 hβr
    (le_trans hpow4 hk1) (le_trans hpow4 hl1) h3'' h4' (hlog46 k hk1) (hlog54 k hk2)
  -- the main term
  have hmain : ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
      B m * B n * w (m * n) ≤ max C₁ 0 * X₀ / (0.46 * log x) ^ 2 := by
    set c0 := 1 / (0.46 * log x * V) with hc0
    have hc0pos : 0 < c0 := by positivity
    calc ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
          B m * B n * w (m * n)
        ≤ ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
          c0 ^ 2 * ((if IsRough (sieveLevel x) m then 1 else 0) *
            (if IsRough (sieveLevel x) n then 1 else 0) * w (m * n)) := by
          apply Finset.sum_le_sum; intro m hm
          apply Finset.sum_le_sum; intro n hn
          obtain ⟨hm1, hm2⟩ := hboxm m hm
          obtain ⟨hn1, hn2⟩ := hboxn n hn
          have e1 := hBle m hm1 hm2
          have e2 := hBle n hn1 hn2
          have hi1 : (0 : ℝ) ≤ (if IsRough (sieveLevel x) m then 1 else 0) := by
            split_ifs <;> norm_num
          have hi2 : (0 : ℝ) ≤ (if IsRough (sieveLevel x) n then 1 else 0) := by
            split_ifs <;> norm_num
          have := mul_le_mul e1 e2 (hB0 n) (by positivity)
          calc B m * B n * w (m * n) ≤ (c0 * (if IsRough (sieveLevel x) m then 1 else 0)) *
                (c0 * (if IsRough (sieveLevel x) n then 1 else 0)) * w (m * n) :=
                mul_le_mul_of_nonneg_right this (hw0 _)
            _ = _ := by ring
      _ = c0 ^ 2 * ∑ m ∈ (Finset.Ico (2 ^ l) (2 ^ (l + 1))).filter
              (fun m => IsRough (sieveLevel x) m),
            ∑ n ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter (fun n => IsRough (sieveLevel x) n),
              w (m * n) := by
          rw [Finset.mul_sum, Finset.sum_filter]
          apply Finset.sum_congr rfl; intro m _
          rw [Finset.sum_filter]
          split_ifs with hm
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro n _
            split_ifs <;> ring
          · simp
      _ ≤ c0 ^ 2 * (C₁ * X₀ * V ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hp46 := Real.rpow_nonneg hx0.le (0.46 : ℝ)
          have hp54 := Real.rpow_nonneg hx0.le (0.54 : ℝ)
          have hpl : (0 : ℝ) ≤ 2 ^ l := by positivity
          have hpk : (0 : ℝ) ≤ 2 ^ k := by positivity
          have := hRP (2 ^ l) (2 ^ k) h3.le h4.le (by linarith) (by linarith) (by linarith)
            (by linarith)
          rw [filter_box_eq, filter_box_eq] at this
          exact this
      _ ≤ c0 ^ 2 * (max C₁ 0 * X₀ * V ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
      _ = max C₁ 0 * X₀ / (0.46 * log x) ^ 2 := by
          rw [hc0]; field_simp
  -- assemble
  have hsplit : ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        R m * R n * w (m * n) =
      ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        (R m - B m) * R n * w (m * n) +
      ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        (R n - B n) * β m * w (n * m) +
      ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        B m * B n * w (m * n) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro m hm
    apply Finset.sum_congr rfl; intro n _
    simp only [hβ, if_pos hm, mul_comm n m]
    ring
  have hcomm : ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        (R n - B n) * β m * w (n * m) =
      ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)),
        (R n - B n) * β m * w (n * m) := Finset.sum_comm
  rw [hcomm] at hsplit
  rw [hsplit]
  simp only [← hR, ← hB, ← hw] at hE₁ hE₂
  have e1 := (abs_le.mp hE₁).2
  have e2 := (abs_le.mp hE₂).2
  have hAx : A * ((2 : ℝ) ^ l * 2 ^ k) * log x ^ (-6 : ℝ) ≤ max A 0 * (2 * x) * log x ^ (-6 : ℝ) :=
    by
    apply mul_le_mul_of_nonneg_right _ hL6
    calc A * ((2 : ℝ) ^ l * 2 ^ k) ≤ max A 0 * ((2 : ℝ) ^ l * 2 ^ k) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max A 0 * (2 * x) := mul_le_mul_of_nonneg_left h4.le (le_max_right _ _)
  have hAx' : A * ((2 : ℝ) ^ k * 2 ^ l) * log x ^ (-6 : ℝ) ≤
      max A 0 * (2 * x) * log x ^ (-6 : ℝ) := by
    rw [mul_comm ((2 : ℝ) ^ k)]; exact hAx
  linarith

lemma rpow_half_mul (x κ : ℝ) (hx : 0 < x) : x ^ (1 / 2 - κ) * x ^ (1 / 2 + κ) = x := by
  rw [← Real.rpow_add hx]; norm_num

open Classical in
/-- Composites with least prime factor above `x^{1/2-κ}` are products of two such factors. -/
lemma composite_to_pairs (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ) (hx : 1 < x) {K : ℕ} (a : Fin K → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hκ' : κ < 0.01) :
    ∑' d : ℕ, (if IsRough (x ^ (1 / 2 - κ)) d ∧ ¬ d.Prime then
        constructionWeight M c u Ψ x a d else 0) ≤
      ∑ m ∈ (Finset.Ico 1 (2 ^ (Nat.log 2 ⌈2 * x⌉₊ + 1))).filter
          (fun m : ℕ => x ^ (1 / 2 - κ) < m ∧ (m : ℝ) < 2 * x ^ (1 / 2 + κ)),
        ∑ n ∈ (Finset.Ico 1 (2 ^ (Nat.log 2 ⌈2 * x⌉₊ + 1))).filter
          (fun m : ℕ => x ^ (1 / 2 - κ) < m ∧ (m : ℝ) < 2 * x ^ (1 / 2 + κ)),
          roughIndicator x 0.4 m * roughIndicator x 0.4 n *
            constructionWeight M c u Ψ x a (m * n) := by
  have hx0 : 0 < x := by linarith
  set N := ⌈2 * x⌉₊ with hN
  set Lm := Nat.log 2 N + 1 with hLm
  have hNLm : N < 2 ^ Lm := Nat.lt_pow_succ_log_self (by norm_num) N
  set Mset := (Finset.Ico 1 (2 ^ Lm)).filter
          (fun m : ℕ => x ^ (1 / 2 - κ) < m ∧ (m : ℝ) < 2 * x ^ (1 / 2 + κ)) with hMset
  set w := constructionWeight M c u Ψ x a with hw
  have hw0 : ∀ d, 0 ≤ w d := constructionWeight_nonneg M c u Ψ hΨ0 x a
  set R := roughIndicator x 0.4 with hR
  have hR0 : ∀ m, 0 ≤ R m := fun m => by simp only [hR, roughIndicator]; split_ifs <;> norm_num
  have h04 : x ^ (0.4 : ℝ) ≤ x ^ (1 / 2 - κ) :=
    Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num; linarith)
  rw [tsum_weight_eq_sum M c u Ψ hΨs x hx0 a]
  set D := (Finset.range N).filter
    (fun d => (IsRough (x ^ (1 / 2 - κ)) d ∧ ¬ d.Prime) ∧ w d ≠ 0) with hD
  have h1 : ∑ d ∈ Finset.range N, (if IsRough (x ^ (1 / 2 - κ)) d ∧ ¬ d.Prime then
      w d else 0) = ∑ d ∈ D, w d := by
    rw [hD, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases h : IsRough (x ^ (1 / 2 - κ)) d ∧ ¬ d.Prime
    · by_cases hw' : w d = 0
      · rw [if_pos h, if_neg (fun h' => h'.2 hw'), hw']
      · rw [if_pos h, if_pos ⟨h, hw'⟩]
    · rw [if_neg h, if_neg (fun h' => h h'.1)]
  rw [h1]
  set φ : ℕ → ℕ × ℕ := fun d => (d.minFac, d / d.minFac) with hφ
  -- properties of `D`
  have hDprop : ∀ d ∈ D, φ d ∈ Mset ×ˢ Mset ∧ R (φ d).1 = 1 ∧ R (φ d).2 = 1 ∧
      (φ d).1 * (φ d).2 = d := by
    intro d hd
    simp only [hD, Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨hdN, ⟨hr, hnp⟩, hwd⟩ := hd
    obtain ⟨hd2, -, hxd, hd2x, -⟩ := constructionWeight_support M c u Ψ hΨs x hx0 a d hwd
    have hd1 : d ≠ 1 := by omega
    have hp := Nat.minFac_prime hd1
    have hpd := Nat.minFac_dvd d
    set p := d.minFac with hpdef
    set q := d / p with hqdef
    have hpq : p * q = d := Nat.mul_div_cancel' hpd
    have hq0 : q ≠ 0 := by intro h; rw [h, mul_zero] at hpq; omega
    have hq1 : q ≠ 1 := by
      intro h; rw [h, mul_one] at hpq; rw [← hpq] at hnp; exact hnp hp
    have hpfac : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩
    have hplow : x ^ (1 / 2 - κ) < p := hr.2 p hpfac
    have hqrough : IsRough (x ^ (1 / 2 - κ)) q := by
      refine ⟨Nat.pos_of_ne_zero hq0, fun r hr' => hr.2 r ?_⟩
      rw [Nat.mem_primeFactors] at hr' ⊢
      exact ⟨hr'.1, Nat.dvd_trans hr'.2.1 (Nat.div_dvd_of_dvd hpd), by omega⟩
    have hqlow : x ^ (1 / 2 - κ) < q := by
      have hqm := Nat.minFac_prime hq1
      have hqf : q.minFac ∈ q.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hqm, Nat.minFac_dvd q, hq0⟩
      have := hqrough.2 _ hqf
      have : (q.minFac : ℝ) ≤ q := by exact_mod_cast Nat.minFac_le (Nat.pos_of_ne_zero hq0)
      linarith
    have hprod : (p : ℝ) * q = d := by exact_mod_cast hpq
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hq0' : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq0
    have hsplit := rpow_half_mul x κ hx0
    have hxpos : 0 < x ^ (1 / 2 - κ) := by positivity
    have hphigh : (p : ℝ) < 2 * x ^ (1 / 2 + κ) := by
      by_contra hc; push_neg at hc
      have : 2 * x ^ (1 / 2 + κ) * x ^ (1 / 2 - κ) ≤ p * q := by
        apply mul_le_mul hc hqlow.le hxpos.le hp0.le
      nlinarith
    have hqhigh : (q : ℝ) < 2 * x ^ (1 / 2 + κ) := by
      by_contra hc; push_neg at hc
      have : x ^ (1 / 2 - κ) * (2 * x ^ (1 / 2 + κ)) ≤ p * q := by
        apply mul_le_mul hplow.le hc (by positivity) hp0.le
      nlinarith
    have hpN : p < 2 ^ Lm := by
      have : p ≤ d := Nat.minFac_le (by omega)
      omega
    have hqN : q < 2 ^ Lm := by
      have : q ≤ d := Nat.div_le_self d p
      omega
    refine ⟨?_, ?_, ?_, hpq⟩
    · simp only [Finset.mem_product, hMset, Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨⟨hp.one_le, hpN⟩, hplow, hphigh⟩, ⟨⟨Nat.pos_of_ne_zero hq0, hqN⟩, hqlow, hqhigh⟩⟩
    · show R p = 1
      simp only [hR, roughIndicator]
      rw [if_pos (isRough_of_prime _ p hp (lt_of_le_of_lt h04 hplow))]
    · show R q = 1
      simp only [hR, roughIndicator]
      rw [if_pos (isRough_mono h04 hqrough)]
  have hinj : Set.InjOn φ (D : Set ℕ) := by
    intro d₁ h₁ d₂ h₂ h
    rw [← (hDprop d₁ h₁).2.2.2, ← (hDprop d₂ h₂).2.2.2, h]
  calc ∑ d ∈ D, w d = ∑ q ∈ D.image φ, R q.1 * R q.2 * w (q.1 * q.2) := by
        rw [Finset.sum_image hinj]
        apply Finset.sum_congr rfl
        intro d hd
        obtain ⟨-, h1, h2, h3⟩ := hDprop d hd
        rw [h1, h2, h3]; ring
    _ ≤ ∑ q ∈ Mset ×ˢ Mset, R q.1 * R q.2 * w (q.1 * q.2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          rw [Finset.mem_image] at hq
          obtain ⟨d, hd, rfl⟩ := hq
          exact (hDprop d hd).1
        · intro q _ _
          exact mul_nonneg (mul_nonneg (hR0 _) (hR0 _)) (hw0 _)
    _ = _ := Finset.sum_product _ _ _

/-- Splitting the pair sum into dyadic boxes. -/
lemma pairs_to_boxes (F : ℕ → ℕ → ℝ) (hF : ∀ m n, 0 ≤ F m n) (x κ : ℝ) (Lm : ℕ) :
    ∑ m ∈ (Finset.Ico 1 (2 ^ Lm)).filter
          (fun m : ℕ => x ^ (1 / 2 - κ) < m ∧ (m : ℝ) < 2 * x ^ (1 / 2 + κ)),
        ∑ n ∈ (Finset.Ico 1 (2 ^ Lm)).filter
          (fun m : ℕ => x ^ (1 / 2 - κ) < m ∧ (m : ℝ) < 2 * x ^ (1 / 2 + κ)), F m n ≤
      ∑ l ∈ (Finset.range Lm).filter (fun l : ℕ => x ^ (1 / 2 - κ) < (2 : ℝ) ^ (l + 1) ∧
          (2 : ℝ) ^ l < 2 * x ^ (1 / 2 + κ)),
        ∑ k ∈ (Finset.range Lm).filter (fun l : ℕ => x ^ (1 / 2 - κ) < (2 : ℝ) ^ (l + 1) ∧
          (2 : ℝ) ^ l < 2 * x ^ (1 / 2 + κ)),
          ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
            F m n := by
  set Mset := (Finset.Ico 1 (2 ^ Lm)).filter
          (fun m : ℕ => x ^ (1 / 2 - κ) < m ∧ (m : ℝ) < 2 * x ^ (1 / 2 + κ))
  set Lset := (Finset.range Lm).filter (fun l : ℕ => x ^ (1 / 2 - κ) < (2 : ℝ) ^ (l + 1) ∧
          (2 : ℝ) ^ l < 2 * x ^ (1 / 2 + κ))
  have hM : ∀ m ∈ Mset, 1 ≤ m ∧ Nat.log 2 m ∈ Lset := by
    intro m hm
    simp only [Mset, Finset.mem_filter, Finset.mem_Ico] at hm
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hm
    refine ⟨h1, ?_⟩
    simp only [Lset, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.log_lt_of_lt_pow (by omega) h2, ?_, ?_⟩
    · have : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
      have : (m : ℝ) < 2 ^ (Nat.log 2 m + 1) := by exact_mod_cast this
      linarith
    · have : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
      have : (2 : ℝ) ^ Nat.log 2 m ≤ m := by exact_mod_cast this
      linarith
  calc ∑ m ∈ Mset, ∑ n ∈ Mset, F m n
      ≤ ∑ m ∈ Mset, ∑ k ∈ Lset, ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), F m n :=
        Finset.sum_le_sum fun m _ => sum_le_sum_scales (F m) (hF m) Mset Lset hM
    _ ≤ ∑ l ∈ Lset, ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ k ∈ Lset,
          ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), F m n :=
        sum_le_sum_scales _ (fun m => Finset.sum_nonneg fun k _ => Finset.sum_nonneg
          fun n _ => hF m n) Mset Lset hM
    _ = _ := by
        apply Finset.sum_congr rfl; intro l _
        exact Finset.sum_comm

set_option maxHeartbeats 1000000 in
open Classical in
/-- The balanced composites (12.33). -/
theorem balanced_cost (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ κ : ℝ, 0 < κ → κ < 0.01 →
    ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        ∑' d : ℕ, (if IsRough (x ^ (1 / 2 - κ)) d ∧ ¬ d.Prime then
            constructionWeight M c u Ψ x a d else 0) ≤
          C₂ * (κ + 1 / log x) * (totalMass M c u Ψ x a / log x) +
            η * (totalMass M c u Ψ x a / log x) := by
  obtain ⟨C₁, hC₁⟩ := rough_pairs_upper_bound M hM h8 Ψ hΨ hΨs hΨ0 hΨ1 hΨi
  set C := max C₁ 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  refine ⟨9 * C / 0.2116 + 1, by positivity, fun κ hκ hκ' => ?_⟩
  obtain ⟨K₀, hK₀⟩ := type_ii_progression M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi
    0.4 0.4 0.46 0.54 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (1 / 4) 2 (by norm_num)
  refine ⟨K₀, fun K hK1 hKK a ha ha' η hη => ?_⟩
  obtain ⟨A, x₁, hA⟩ := hK₀ K hK1 hKK a ha ha'
  obtain ⟨x₂, hx₂⟩ := hC₁ c u hc hu hcu hcop K hK1 a ha ha'
  obtain ⟨-, c₁, c₂, hc₁, hc₂, hwfd⟩ :=
    weighted_family_distribution M hM h8 Ψ hΨ hΨs hΨ0 hΨ1 hΨi
  obtain ⟨x₃, hx₃⟩ := hwfd c u hc hu hcu hcop K hK1 a ha ha'
  obtain ⟨CJ, hCJ⟩ := harmonic_mass M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi K hK1
  obtain ⟨x₄, hx₄⟩ := hCJ a ha ha' 1 one_pos
  set L₀ : ℝ := max 3 (8 * max A 0 / (η * 1 * c₁)) with hL₀
  have hev : ∀ᶠ x : ℝ in atTop, L₀ ≤ log x ∧ sieveLevel x < x ^ (0.4 : ℝ) ∧
      1 ≤ 0.46 * log x * mertensProduct (sieveLevel x) ∧ (4 : ℝ) ≤ x ^ (0.03 : ℝ) ∧
      x₁ ≤ x ∧ x₂ ≤ x ∧ x₃ ≤ x ∧ x₄ ≤ x ∧ 1 < x :=
    (Real.tendsto_log_atTop.eventually_ge_atTop L₀).and
      ((eventually_sieveLevel_lt 0.4 (by norm_num)).and (eventually_mertens_lower.and
      (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.03)).eventually_ge_atTop 4).and
      ((eventually_ge_atTop x₁).and ((eventually_ge_atTop x₂).and ((eventually_ge_atTop x₃).and
        ((eventually_ge_atTop x₄).and (eventually_gt_atTop 1))))))))
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨hLx, hW, hV, h003, hx1, hx2, hx3, hx4, hx1'⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hL : 0 < log x := Real.log_pos hx1'
  have hL3 : 3 ≤ log x := le_trans (le_max_left _ _) hLx
  have hLA : 8 * max A 0 / (η * 1 * c₁) ≤ log x := le_trans (le_max_right _ _) hLx
  set X₀ := totalMass M c u Ψ x a with hX₀
  have hX0 : 0 ≤ X₀ := totalMass_nonneg M c u Ψ hΨ0 x a
  set w := constructionWeight M c u Ψ x a with hw
  have hw0 : ∀ d, 0 ≤ w d := constructionWeight_nonneg M c u Ψ hΨ0 x a
  set R := roughIndicator x 0.4 with hR
  have hR0 : ∀ m, 0 ≤ R m := fun m => by simp only [hR, roughIndicator]; split_ifs <;> norm_num
  set Lm := Nat.log 2 ⌈2 * x⌉₊ + 1 with hLm
  set Lset := (Finset.range Lm).filter (fun l : ℕ => x ^ (1 / 2 - κ) < (2 : ℝ) ^ (l + 1) ∧
          (2 : ℝ) ^ l < 2 * x ^ (1 / 2 + κ)) with hLset
  set Bnd := C * X₀ / (0.46 * log x) ^ 2 + 2 * (max A 0 * (2 * x) * log x ^ (-6 : ℝ)) with hBnd
  have hL6 : 0 ≤ log x ^ (-6 : ℝ) := Real.rpow_nonneg hL.le _
  have hBnd0 : 0 ≤ Bnd := by positivity
  -- box scales
  have hp49 : x ^ (0.49 : ℝ) ≤ x ^ (1 / 2 - κ) :=
    Real.rpow_le_rpow_of_exponent_le hx1'.le (by norm_num; linarith)
  have hp51 : x ^ (1 / 2 + κ) ≤ x ^ (0.51 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1'.le (by norm_num; linarith)
  have hp46 : 2 * x ^ (0.46 : ℝ) ≤ x ^ (0.49 : ℝ) := by
    rw [show (0.49 : ℝ) = 0.46 + 0.03 by norm_num, Real.rpow_add hx0]
    have : 0 ≤ x ^ (0.46 : ℝ) := by positivity
    nlinarith
  have hp54 : 4 * x ^ (0.51 : ℝ) ≤ x ^ (0.54 : ℝ) := by
    rw [show (0.54 : ℝ) = 0.51 + 0.03 by norm_num, Real.rpow_add hx0]
    have : 0 ≤ x ^ (0.51 : ℝ) := by positivity
    nlinarith
  have hscale : ∀ l ∈ Lset, x ^ (0.46 : ℝ) ≤ 2 ^ l ∧ 2 * (2 : ℝ) ^ l ≤ x ^ (0.54 : ℝ) := by
    intro l hl
    simp only [hLset, Finset.mem_filter] at hl
    obtain ⟨-, h1, h2⟩ := hl
    rw [pow_succ] at h1
    constructor <;> linarith
  have hbox : ∀ l ∈ Lset, ∀ k ∈ Lset,
      ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        R m * R n * w (m * n) ≤
      if x / 4 < (2 : ℝ) ^ l * 2 ^ k ∧ (2 : ℝ) ^ l * 2 ^ k < 2 * x then Bnd else 0 := by
    intro l hl k hk
    split_ifs with hrel
    · obtain ⟨hl1, hl2⟩ := hscale l hl
      obtain ⟨hk1, hk2⟩ := hscale k hk
      exact box_bound M c u Ψ hΨ0 x a A C₁ hx1'
        (fun Hm Hn h1 h2 h3 h4 J hJ hJs h5 h6 β hβ1 hβs =>
          hA x hx1 Hm Hn h1 h2 h3 h4 J hJ hJs h5 h6 β hβ1 hβs)
        (hx₂ x hx2) hV hW.le l k hl1 hl2 hk1 hk2 hrel.1 hrel.2
    · apply le_of_eq
      apply Finset.sum_eq_zero; intro m hm
      apply Finset.sum_eq_zero; intro n hn
      by_contra hne
      have hwne : w (m * n) ≠ 0 := fun h => hne (by rw [h, mul_zero])
      obtain ⟨-, -, hxmn, hmn2x, -⟩ := constructionWeight_support M c u Ψ hΨs x hx0 a _ hwne
      push_cast at hxmn hmn2x
      apply hrel
      rw [Finset.mem_Ico] at hm hn
      have hm1 : (2 : ℝ) ^ l ≤ m := by exact_mod_cast hm.1
      have hm2 : (m : ℝ) < 2 * 2 ^ l := by
        have : (m : ℝ) < 2 ^ (l + 1) := by exact_mod_cast hm.2
        rw [pow_succ] at this; linarith
      have hn1 : (2 : ℝ) ^ k ≤ n := by exact_mod_cast hn.1
      have hn2 : (n : ℝ) < 2 * 2 ^ k := by
        have : (n : ℝ) < 2 ^ (k + 1) := by exact_mod_cast hn.2
        rw [pow_succ] at this; linarith
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      constructor
      · have : (m : ℝ) * n ≤ (2 * 2 ^ l) * (2 * 2 ^ k) := mul_le_mul hm2.le hn2.le hn0 (by positivity)
        linarith
      · have : (2 : ℝ) ^ l * 2 ^ k ≤ m * n := mul_le_mul hm1 hn1 (by positivity) hm0
        linarith
  -- assemble
  have hred := composite_to_pairs M c u Ψ hΨs hΨ0 x hx1' a κ hκ hκ'
  have hpairs := pairs_to_boxes (fun m n => R m * R n * w (m * n))
    (fun m n => mul_nonneg (mul_nonneg (hR0 m) (hR0 n)) (hw0 _)) x κ Lm
  have hsum : ∑ l ∈ Lset, ∑ k ∈ Lset,
      ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        R m * R n * w (m * n) ≤ (3 + 3 * κ * log x) * (3 * Bnd) := by
    calc _ ≤ ∑ l ∈ Lset, ∑ k ∈ Lset,
          (if x / 4 < (2 : ℝ) ^ l * 2 ^ k ∧ (2 : ℝ) ^ l * 2 ^ k < 2 * x then Bnd else 0) :=
          Finset.sum_le_sum fun l hl => Finset.sum_le_sum fun k hk => hbox l hl k hk
      _ ≤ ∑ l ∈ Lset, 3 * Bnd := by
          apply Finset.sum_le_sum; intro l _
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ hBnd0
          exact_mod_cast card_relevant_le x hx0 l Lset
      _ = (Lset.card : ℝ) * (3 * Bnd) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (3 + 3 * κ * log x) * (3 * Bnd) :=
          mul_le_mul_of_nonneg_right (card_scales_le x κ hx1' hκ _) (by positivity)
  have htot := le_trans hred (le_trans hpairs hsum)
  -- the error term
  have hJ := (hx₄ x hx4).2.2.1
  have hXlow := (hx₃ x hx3).1
  have herr := typeII_error_small x (log x) (max A 0) (2 * log x) η 1 c₁ X₀
    (harmonicMass x a) (by linarith) hx0 (le_max_right _ _) (by positivity) le_rfl hη one_pos
    hc₁ hJ hXlow hLA
  have hcoef : (3 + 3 * κ * log x) * 3 * 2 ≤ (2 * log x) ^ 2 := by nlinarith
  have herr' : (3 + 3 * κ * log x) * 3 * (2 * (max A 0 * (2 * x) * log x ^ (-6 : ℝ))) ≤
      η * (X₀ / log x) := by
    have h0 : 0 ≤ max A 0 * (2 * x) * log x ^ (-6 : ℝ) := by positivity
    calc (3 + 3 * κ * log x) * 3 * (2 * (max A 0 * (2 * x) * log x ^ (-6 : ℝ)))
        = (3 + 3 * κ * log x) * 3 * 2 * (max A 0 * (2 * x) * log x ^ (-6 : ℝ)) := by ring
      _ ≤ (2 * log x) ^ 2 * (max A 0 * (2 * x) * log x ^ (-6 : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoef h0
      _ ≤ η * (1 * X₀ / log x) := herr
      _ = η * (X₀ / log x) := by ring
  have hmain : (3 + 3 * κ * log x) * 3 * (C * X₀ / (0.46 * log x) ^ 2) ≤
      (9 * C / 0.2116 + 1) * (κ + 1 / log x) * (X₀ / log x) := by
    have e : (3 + 3 * κ * log x) * 3 * (C * X₀ / (0.46 * log x) ^ 2) =
        9 * C / 0.2116 * (κ + 1 / log x) * (X₀ / log x) := by
      field_simp; ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have : (3 + 3 * κ * log x) * (3 * Bnd) =
      (3 + 3 * κ * log x) * 3 * (C * X₀ / (0.46 * log x) ^ 2) +
      (3 + 3 * κ * log x) * 3 * (2 * (max A 0 * (2 * x) * log x ^ (-6 : ℝ))) := by
    rw [hBnd]; ring
  linarith

end ArtinPrimitiveRoots.P21balanced_cost

open ArtinPrimitiveRoots ArtinPrimitiveRoots.P21balanced_cost Real in
open Classical in
theorem solution (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ κ : ℝ, 0 < κ → κ < 0.01 →
    ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        ∑' d : ℕ, (if IsRough (x ^ (1 / 2 - κ)) d ∧ ¬ d.Prime then
            constructionWeight M c u Ψ x a d else 0) ≤
          C₂ * (κ + 1 / log x) * (totalMass M c u Ψ x a / log x) +
            η * (totalMass M c u Ψ x a / log x) :=
  ArtinPrimitiveRoots.P21balanced_cost.balanced_cost M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi
