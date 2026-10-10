-- Prove2me | solution 1 for ArtinPrimitiveRoots.bin_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:20:16.777478+00:00
-- url     : https://prove2.me/submissions/85ed079b-c606-4f5b-b779-766f947e266b

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_harmonic_mass
import Theorems.Thm_ArtinPrimitiveRoots_mass_conditioned_on_divisor
import Theorems.Thm_ArtinPrimitiveRoots_type_ii_progression
import Theorems.Thm_ArtinPrimitiveRoots_weighted_family_distribution

namespace ArtinPrimitiveRoots.P21bin_cost

open Real Filter Topology MeasureTheory

theorem singularSeries_pos (M : ℕ) : 0 < singularSeries M := by
  unfold singularSeries
  have hp3 : ∀ p : {p : ℕ // p.Prime ∧ 2 < p}, (3 : ℝ) ≤ p.1 := fun p => by
    exact_mod_cast p.2.2
  have hg : Summable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => -(1 / ((p.1 : ℝ) - 1) ^ 2)) := by
    apply Summable.neg
    have hs : Summable (fun n : ℕ => 9 / 4 * (1 / (n : ℝ) ^ 2)) :=
      (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
    have hs' := hs.comp_injective (Subtype.val_injective (p := fun p : ℕ => p.Prime ∧ 2 < p))
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hs'
    · have := hp3 p
      positivity
    · have h3 := hp3 p
      simp only [Function.comp]
      rw [div_le_iff₀ (by nlinarith)]
      field_simp
      nlinarith
  have hpos : ∀ p : {p : ℕ // p.Prime ∧ 2 < p}, 0 < 1 + -(1 / ((p.1 : ℝ) - 1) ^ 2) := by
    intro p
    have h3 := hp3 p
    have : 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
      nlinarith
    linarith
  have hprod : 0 < ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2) := by
    have := Real.rexp_tsum_eq_tprod hpos (Real.summable_log_one_add_of_summable hg)
    simp only [← sub_eq_add_neg] at this
    rw [← this]
    exact Real.exp_pos _
  apply mul_pos (mul_pos two_pos hprod)
  apply Finset.prod_pos
  intro p hp
  simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
  apply inv_pos.mpr
  have : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

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

lemma totalMass_nonneg (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ) {K : ℕ}
    (a : Fin K → ℝ) : 0 ≤ totalMass M c u Ψ x a :=
  tsum_nonneg fun d => constructionWeight_nonneg M c u Ψ hΨ0 x a d

/-- The integration region of `D_{γ,j}` with `n = j - 1` variables. -/
def regionD (n : ℕ) (γ w : ℝ) : Set (Fin n → ℝ) :=
  {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ}

/-- The integrand of `D_{γ,j}`. -/
noncomputable def integrandD (n : ℕ) (w : ℝ) (t : Fin n → ℝ) : ℝ :=
  (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹

lemma regionD_closed (n : ℕ) (γ w : ℝ) : IsClosed (regionD n γ w) := by
  unfold regionD
  rw [Set.setOf_and, Set.ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

lemma measurable_integrandD (n : ℕ) (w : ℝ) : Measurable (integrandD n w) := by
  unfold integrandD
  apply Measurable.mul
  · exact (measurable_const.sub (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)).inv
  · exact Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).inv

lemma regionD_empty (n : ℕ) (γ w : ℝ) (h : w < (n + 1) * γ) : regionD n γ w = ∅ := by
  ext t
  simp only [regionD, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
  intro ht
  have : ∑ _i : Fin n, γ ≤ ∑ i, t i := Finset.sum_le_sum fun i _ => ht i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  linarith

lemma sum_hyperplane_null (n : ℕ) (hn : 0 < n) (c : ℝ) :
    volume {t : Fin n → ℝ | ∑ i, t i = c} = 0 := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
  have hL : ∀ t, L t = ∑ i, t i := fun t => by
    simp [L, LinearMap.sum_apply]
  let i₀ : Fin n := ⟨0, hn⟩
  let p : Fin n → ℝ := Pi.single i₀ c
  have hp : ∑ i, p i = c := by simp [p]
  let s : AffineSubspace ℝ (Fin n → ℝ) := AffineSubspace.mk' p (LinearMap.ker L)
  have hsub : {t : Fin n → ℝ | ∑ i, t i = c} ⊆ s := by
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht
    show t ∈ s
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, map_sub, hL, hL, ht, hp, sub_self]
  have hne : s ≠ ⊤ := by
    intro htop
    have hmem : p + Pi.single i₀ 1 ∈ s := by rw [htop]; exact AffineSubspace.mem_top _ _ _
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, map_sub, hL, hL] at hmem
    simp [p, Finset.sum_add_distrib] at hmem
  exact measure_mono_null hsub (Measure.addHaar_affineSubspace volume s hne)

/-- Continuity of `∫_{regionD n γ w} integrandD n w`. -/
lemma continuousAt_integralD (n : ℕ) (hn : 0 < n) (γ₀ w₀ : ℝ) (hγ₀ : 0 < γ₀) (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => ∫ t in regionD n p.1 p.2, integrandD n p.2 t) (γ₀, w₀) := by
  have hmeas : ∀ γ w, MeasurableSet (regionD n γ w) := fun γ w =>
    (regionD_closed n γ w).measurableSet
  simp_rw [← integral_indicator (hmeas _ _)]
  set C : ℝ := (2 / γ₀) ^ (n + 1) with hC
  set box : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (γ₀ / 2) (2 * w₀)) with hbox
  have hboxm : MeasurableSet box := (isClosed_set_pi fun _ _ => isClosed_Icc).measurableSet
  have hnbhd : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), γ₀ / 2 < p.1 ∧ p.2 < 2 * w₀ := by
    have h1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), γ₀ / 2 < p.1 :=
      continuous_fst.continuousAt.eventually (lt_mem_nhds (by linarith))
    have h2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), p.2 < 2 * w₀ :=
      continuous_snd.continuousAt.eventually (gt_mem_nhds (by linarith))
    exact h1.and h2
  apply continuousAt_of_dominated (bound := box.indicator (fun _ => C))
  · exact Eventually.of_forall fun p =>
      ((measurable_integrandD n p.2).indicator (hmeas _ _)).aestronglyMeasurable
  · filter_upwards [hnbhd] with p hp
    refine Eventually.of_forall fun t => ?_
    by_cases ht : t ∈ regionD n p.1 p.2
    · rw [Set.indicator_of_mem ht]
      obtain ⟨ht1, ht2⟩ := ht
      have htpos : ∀ i, γ₀ / 2 < t i := fun i => lt_of_lt_of_le hp.1 (ht1 i)
      have htle : ∀ i, t i ≤ 2 * w₀ := by
        intro i
        have : t i ≤ ∑ j, t j :=
          Finset.single_le_sum (fun j _ => le_trans (by linarith) (htpos j).le) (Finset.mem_univ i)
        linarith [hp.1, hp.2]
      have htbox : t ∈ box := by
        simp only [hbox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
        exact fun i => ⟨(htpos i).le, htle i⟩
      rw [Set.indicator_of_mem htbox]
      have hden : γ₀ / 2 < p.2 - ∑ i, t i := by linarith [hp.1]
      unfold integrandD
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (by linarith))
        (Finset.prod_nonneg fun i _ => inv_nonneg.mpr (by linarith [htpos i])))]
      rw [hC, pow_succ']
      apply mul_le_mul
      · rw [inv_le_comm₀ (by linarith) (by positivity)]
        rw [inv_div]; exact hden.le
      · calc ∏ i, (t i)⁻¹ ≤ ∏ _i : Fin n, 2 / γ₀ := by
              apply Finset.prod_le_prod (fun i _ => inv_nonneg.mpr (by linarith [htpos i]))
              intro i _
              rw [inv_le_comm₀ (by linarith [htpos i]) (by positivity), inv_div]
              exact (htpos i).le
          _ = (2 / γ₀) ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      · exact Finset.prod_nonneg fun i _ => inv_nonneg.mpr (by linarith [htpos i])
      · positivity
    · rw [Set.indicator_of_notMem ht, norm_zero]
      apply Set.indicator_nonneg
      intro _ _; positivity
  · apply (integrableOn_const ?_).integrable_indicator hboxm
    exact ((isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top).ne
  · -- continuity off the boundary hyperplanes
    have hnull1 : ∀ᵐ t : Fin n → ℝ, ∀ i, t i ≠ γ₀ := by
      rw [ae_all_iff]
      intro i
      have := Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℝ)) i γ₀
      rwa [← volume_pi] at this
    have hnull2 : ∀ᵐ t : Fin n → ℝ, ∑ i, t i ≠ w₀ - γ₀ :=
      compl_mem_ae_iff.mpr (sum_hyperplane_null n hn (w₀ - γ₀))
    filter_upwards [hnull1, hnull2] with t ht1 ht2
    by_cases hin : t ∈ regionD n γ₀ w₀
    · obtain ⟨hin1, hin2⟩ := hin
      have hs1 : ∀ i, γ₀ < t i := fun i => lt_of_le_of_ne (hin1 i) (ht1 i).symm
      have hs2 : ∑ i, t i < w₀ - γ₀ := lt_of_le_of_ne hin2 ht2
      have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), t ∈ regionD n p.1 p.2 := by
        have hmin : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), ∀ i, p.1 < t i :=
          Filter.eventually_all.mpr fun i =>
            continuous_fst.continuousAt.eventually (gt_mem_nhds (hs1 i))
        have hsum : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), ∑ i, t i < p.2 - p.1 :=
          (continuous_snd.sub continuous_fst).continuousAt.eventually (lt_mem_nhds hs2)
        filter_upwards [hmin, hsum] with p h1 h2
        exact ⟨fun i => (h1 i).le, h2.le⟩
      have hcont : ContinuousAt (fun p : ℝ × ℝ => integrandD n p.2 t) (γ₀, w₀) := by
        unfold integrandD
        apply ContinuousAt.mul _ continuousAt_const
        apply ContinuousAt.inv₀ (continuous_snd.sub continuous_const).continuousAt
        show w₀ - ∑ i, t i ≠ 0
        linarith
      refine hcont.congr ?_
      filter_upwards [hev] with p hp
      rw [Set.indicator_of_mem hp]
    · have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), t ∉ regionD n p.1 p.2 := by
        simp only [regionD, Set.mem_ofPred_eq, not_and_or, not_forall, not_le] at hin ⊢
        rcases hin with ⟨i, hi⟩ | hs
        · have : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), t i < p.1 :=
            continuous_fst.continuousAt.eventually (lt_mem_nhds hi)
          filter_upwards [this] with p hp
          exact Or.inl ⟨i, hp⟩
        · have : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), p.2 - p.1 < ∑ i, t i :=
            (continuous_snd.sub continuous_fst).continuousAt.eventually (gt_mem_nhds hs)
          filter_upwards [this] with p hp
          exact Or.inr hp
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hev] with p hp
      rw [Set.indicator_of_notMem hp]

lemma roughDensityTerm_succ_succ (γ w : ℝ) (j : ℕ) :
    roughDensityTerm γ w (j + 2) =
      (1 / ((j + 2).factorial : ℝ)) * ∫ t in regionD (j + 1) γ w, integrandD (j + 1) w t := rfl

theorem roughDensity_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => roughDensity p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
  intro p₀ hp₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨γ₀, w₀⟩ := p₀
  simp only [Set.mem_prod, Set.mem_Ioi] at hp₀
  obtain ⟨hγ₀, hw₀⟩ := hp₀
  set N : ℕ := ⌈4 * w₀ / γ₀⌉₊ + 2 with hN
  have hnbhd : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), γ₀ / 2 < p.1 ∧ p.2 < 2 * w₀ ∧ 0 < p.2 := by
    have h1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), γ₀ / 2 < p.1 :=
      continuous_fst.continuousAt.eventually (lt_mem_nhds (by linarith))
    have h2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), p.2 < 2 * w₀ :=
      continuous_snd.continuousAt.eventually (gt_mem_nhds (by linarith))
    have h3 : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), 0 < p.2 :=
      continuous_snd.continuousAt.eventually (lt_mem_nhds hw₀)
    exact h1.and (h2.and h3)
  have heq : (fun p : ℝ × ℝ => roughDensity p.1 p.2) =ᶠ[𝓝 (γ₀, w₀)]
      fun p => ∑ j ∈ Finset.range N, roughDensityTerm p.1 p.2 j := by
    filter_upwards [hnbhd] with p hp
    unfold roughDensity
    apply tsum_eq_sum
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    rw [roughDensityTerm_succ_succ, regionD_empty, Measure.restrict_empty, integral_zero_measure,
      mul_zero]
    have hceil := Nat.le_ceil (4 * w₀ / γ₀)
    rw [div_le_iff₀ hγ₀] at hceil
    have hk : (N : ℝ) ≤ k + 2 := by exact_mod_cast hj
    have hN' : (N : ℝ) = ⌈4 * w₀ / γ₀⌉₊ + 2 := by rw [hN]; push_cast; ring
    push_cast
    have : (⌈4 * w₀ / γ₀⌉₊ : ℝ) * (γ₀ / 2) < (k + 1 + 1) * p.1 := by
      have h0 : (0 : ℝ) ≤ ⌈4 * w₀ / γ₀⌉₊ := Nat.cast_nonneg _
      nlinarith [hp.1]
    nlinarith [hp.2.1]
  refine ContinuousAt.congr ?_ heq.symm
  have hterm : ∀ j, ContinuousAt (fun p : ℝ × ℝ => roughDensityTerm p.1 p.2 j) (γ₀, w₀) := by
    intro j
    match j with
    | 0 => simp only [roughDensityTerm]; exact continuousAt_const
    | 1 =>
      simp only [roughDensityTerm]
      exact (continuousAt_const.div continuous_snd.continuousAt hw₀.ne')
    | k + 2 =>
      simp only [roughDensityTerm_succ_succ]
      exact continuousAt_const.mul
        (continuousAt_integralD (k + 1) (Nat.succ_pos k) γ₀ w₀ hγ₀ hw₀)
  exact tendsto_finsetSum _ fun j _ => hterm j

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

lemma sum_dyadic (f : ℕ → ℝ) (L : ℕ) :
    ∑ l ∈ Finset.range L, ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), f m =
      ∑ m ∈ Finset.Ico 1 (2 ^ L), f m := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    exact Finset.sum_Ico_consecutive f (Nat.one_le_two_pow) (Nat.pow_le_pow_right two_pos
      (Nat.le_succ L))

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

lemma isRough_mul_prime_iff (y : ℝ) (m n : ℕ) (hn : n.Prime) (hyn : y < n) :
    IsRough y (m * n) ↔ IsRough y m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [IsRough]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hm, fun p hp => h p ?_⟩
    rw [Nat.primeFactors_mul hm.ne' hn.ne_zero]
    exact Finset.mem_union_left _ hp
  · rintro ⟨-, h⟩
    refine ⟨Nat.mul_pos hm hn.pos, fun p hp => ?_⟩
    rw [Nat.primeFactors_mul hm.ne' hn.ne_zero, hn.primeFactors, Finset.mem_union,
      Finset.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact h p hp
    · exact hyn

open Classical in
lemma tsum_rough_mul_eq (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (x : ℝ) {K : ℕ} (a : Fin K → ℝ)
    (y : ℝ) (n : ℕ) (hn : n.Prime) (hyn : y < n) :
    ∑' m : ℕ, (if IsRough y m then constructionWeight M c u Ψ x a (m * n) else 0) =
      ∑' d : ℕ, (if n ∣ d ∧ IsRough y d then constructionWeight M c u Ψ x a d else 0) := by
  have hinj : Function.Injective (fun m : ℕ => m * n) :=
    fun m₁ m₂ h => Nat.eq_of_mul_eq_mul_right hn.pos h
  set f : ℕ → ℝ := fun d =>
    if n ∣ d ∧ IsRough y d then constructionWeight M c u Ψ x a d else 0 with hf
  have hsupp : Function.support f ⊆ Set.range (fun m : ℕ => m * n) := by
    intro d hd
    rw [Function.mem_support] at hd
    by_cases hnd : n ∣ d
    · exact ⟨d / n, Nat.div_mul_cancel hnd⟩
    · exfalso; apply hd; simp only [hf]; rw [if_neg (fun h => hnd h.1)]
  calc ∑' m : ℕ, (if IsRough y m then constructionWeight M c u Ψ x a (m * n) else 0)
      = ∑' m : ℕ, f (m * n) := by
        apply tsum_congr
        intro m
        simp only [hf, isRough_mul_prime_iff y m n hn hyn, Dvd.intro_left m rfl, true_and]
    _ = ∑' d : ℕ, f d := hinj.tsum_eq hsupp

lemma natLog_bound (x : ℝ) (hx : 1 ≤ x) :
    ((Nat.log 2 ⌈2 * x⌉₊ + 1 : ℕ) : ℝ) * log 2 ≤ log x + log 3 + log 2 := by
  have hN : ⌈2 * x⌉₊ ≠ 0 := by
    have : 0 < ⌈2 * x⌉₊ := Nat.ceil_pos.mpr (by linarith)
    omega
  have h1 := Nat.pow_log_le_self 2 hN
  have h2 : ((2 : ℝ)) ^ (Nat.log 2 ⌈2 * x⌉₊) ≤ ⌈2 * x⌉₊ := by exact_mod_cast h1
  have h3 : (⌈2 * x⌉₊ : ℝ) ≤ 3 * x := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 2 * x)
    linarith
  have h4 : log ((2 : ℝ) ^ (Nat.log 2 ⌈2 * x⌉₊)) ≤ log (3 * x) :=
    Real.log_le_log (by positivity) (le_trans h2 h3)
  rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith)] at h4
  push_cast
  linarith

lemma block_decomp (h : ℕ → ℕ → ℝ) (L : ℕ) :
    ∑ n ∈ Finset.Ico 1 (2 ^ L), ∑ m ∈ Finset.Ico 1 (2 ^ L), h m n =
      ∑ k ∈ Finset.range L, ∑ l ∈ Finset.range L,
        ∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), h m n := by
  rw [← sum_dyadic]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  rw [← sum_dyadic]

lemma isRough_of_prime (y : ℝ) (n : ℕ) (hn : n.Prime) (hyn : y < n) : IsRough y n :=
  ⟨hn.pos, fun p hp => by rw [hn.primeFactors, Finset.mem_singleton] at hp; rw [hp]; exact hyn⟩

lemma weight_zero (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (x : ℝ) {K : ℕ} (a : Fin K → ℝ) :
    constructionWeight M c u Ψ x a 0 = 0 := by
  unfold constructionWeight; simp

open Classical in
/-- One dyadic block of the bin sum (§12.4). -/
lemma bin_block (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (κ b γ γ' A : ℝ) (hκ : 0 < κ) (hb : 0 < b) (hbγ : b ≤ γ)
    (hγγ' : γ < γ') (hγ' : γ' ≤ 1 / 2 - κ)
    (hT : ∀ Hm Hn : ℝ, x ^ (b / 2) ≤ Hm → x ^ (b / 2) ≤ Hn → 1 / 4 * x ≤ Hm * Hn →
      Hm * Hn ≤ 2 * x →
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc Hm (2 * Hm) →
      1 / 2 + κ / 2 ≤ log Hm / log x → log (2 * Hm) / log x ≤ 1 - b / 2 →
      ∀ β : ℕ → ℂ, (∀ n, ‖β n‖ ≤ 1) →
        (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
      ‖∑ m ∈ (Finset.range (⌊2 * Hm⌋₊ + 1)).filter (fun m : ℕ => (m : ℝ) ∈ J),
          ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
          ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) * β n *
            (constructionWeight M c u Ψ x a (m * n) : ℂ)‖ ≤ A * (Hm * Hn) * log x ^ (-6 : ℝ))
    (hx : 1 < x) (hC1 : 2 * x ^ (b / 2) ≤ x ^ γ) (hC2 : log 2 ≤ κ / 2 * log x)
    (hC3 : log 4 ≤ b / 2 * log x) (hC4 : sieveLevel x < x ^ γ) (P : Finset ℕ)
    (hPmem : ∀ n ∈ P, n.Prime ∧ x ^ γ < n ∧ (n : ℝ) ≤ x ^ γ') (k l : ℕ) :
    |∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        (roughIndicator x γ m - roughProxy x γ m) * (if n ∈ P then 1 else 0) *
          constructionWeight M c u Ψ x a (m * n)| ≤
      max A 0 * (2 * x) * log x ^ (-6 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < log x := Real.log_pos hx
  have hL6 : 0 ≤ log x ^ (-6 : ℝ) := Real.rpow_nonneg hL.le _
  set β : ℕ → ℝ := fun n => if n ∈ P then 1 else 0 with hβ
  set w := constructionWeight M c u Ψ x a with hw
  by_cases hex : ∃ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∃ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
      β n ≠ 0 ∧ w (m * n) ≠ 0
  · obtain ⟨m₀, hm₀, n₀, hn₀, hβ₀, hw₀⟩ := hex
    have hn₀P : n₀ ∈ P := by
      by_contra hc; apply hβ₀; simp only [hβ, if_neg hc]
    obtain ⟨hn₀p, hn₀lo, hn₀hi⟩ := hPmem n₀ hn₀P
    obtain ⟨-, -, hxmn, hmn2x, -⟩ := constructionWeight_support M c u Ψ hΨs x hx0 a _ hw₀
    push_cast at hxmn hmn2x
    rw [Finset.mem_Ico] at hm₀ hn₀
    have hm1 : (2 : ℝ) ^ l ≤ m₀ := by exact_mod_cast hm₀.1
    have hm2 : (m₀ : ℝ) < 2 * 2 ^ l := by
      have : (m₀ : ℝ) < 2 ^ (l + 1) := by exact_mod_cast hm₀.2
      rw [pow_succ] at this; linarith
    have hk1 : (2 : ℝ) ^ k ≤ n₀ := by exact_mod_cast hn₀.1
    have hk2 : (n₀ : ℝ) < 2 * 2 ^ k := by
      have : (n₀ : ℝ) < 2 ^ (k + 1) := by exact_mod_cast hn₀.2
      rw [pow_succ] at this; linarith
    have hn₀pos : (0 : ℝ) < n₀ := by exact_mod_cast hn₀p.pos
    have hHl : (0 : ℝ) < 2 ^ l := by positivity
    have hHk : (0 : ℝ) < 2 ^ k := by positivity
    have hm₀pos : (0 : ℝ) < m₀ := lt_of_lt_of_le hHl hm1
    have h3 : 1 / 4 * x ≤ 2 ^ l * 2 ^ k := by
      have : (m₀ : ℝ) * n₀ ≤ (2 * 2 ^ l) * (2 * 2 ^ k) :=
        mul_le_mul hm2.le hk2.le hn₀pos.le (by positivity)
      linarith
    have h4 : (2 : ℝ) ^ l * 2 ^ k ≤ 2 * x := by
      have : (2 : ℝ) ^ l * 2 ^ k ≤ m₀ * n₀ := mul_le_mul hm1 hk1 hHk.le hm₀pos.le
      linarith
    have h2 : x ^ (b / 2) ≤ 2 ^ k := by linarith
    have hlogn : log n₀ ≤ γ' * log x := by
      have := Real.log_le_log hn₀pos hn₀hi
      rwa [Real.log_rpow hx0] at this
    have hlogn' : γ * log x < log n₀ := by
      have := Real.log_lt_log (by positivity) hn₀lo
      rwa [Real.log_rpow hx0] at this
    have hlogmn : log x < log m₀ + log n₀ := by
      rw [← Real.log_mul hm₀pos.ne' hn₀pos.ne']; exact Real.log_lt_log hx0 hxmn
    have hlogmn2 : log m₀ + log n₀ < log 2 + log x := by
      rw [← Real.log_mul hm₀pos.ne' hn₀pos.ne', ← Real.log_mul (by norm_num) hx0.ne']
      exact Real.log_lt_log (by positivity) hmn2x
    have hlogHm : log m₀ - log 2 < log (2 ^ l) := by
      rw [← Real.log_div hm₀pos.ne' (by norm_num)]
      exact Real.log_lt_log (by positivity) (by linarith)
    have hlogHm2 : log (2 * 2 ^ l) ≤ log m₀ + log 2 := by
      rw [← Real.log_mul hm₀pos.ne' (by norm_num)]
      exact Real.log_le_log (by positivity) (by linarith)
    have hγ'L : γ' * log x ≤ (1 / 2 - κ) * log x := mul_le_mul_of_nonneg_right hγ' hL.le
    have hbL : b * log x ≤ γ * log x := mul_le_mul_of_nonneg_right hbγ hL.le
    have h5' : (1 / 2 + κ / 2) * log x ≤ log (2 ^ l) := by linarith
    have h5 : 1 / 2 + κ / 2 ≤ log (2 ^ l) / log x := by rw [le_div_iff₀ hL]; exact h5'
    have h6 : log (2 * 2 ^ l) / log x ≤ 1 - b / 2 := by
      rw [div_le_iff₀ hL]
      have : log 4 = 2 * log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    have h1 : x ^ (b / 2) ≤ 2 ^ l := by
      have hb2 : b / 2 * log x ≤ (1 / 2 + κ / 2) * log x := by
        apply mul_le_mul_of_nonneg_right _ hL.le; linarith
      have : log (x ^ (b / 2)) ≤ log (2 ^ l) := by
        rw [Real.log_rpow hx0]; linarith
      exact (Real.log_le_log_iff (by positivity) (by positivity)).mp this
    have hβ1 : ∀ n, |β n| ≤ 1 := fun n => by
      simp only [hβ]; split_ifs <;> norm_num
    have hβr : ∀ n, β n ≠ 0 → IsRough (sieveLevel x) n := by
      intro n hn
      have hnP : n ∈ P := by by_contra hc; apply hn; simp only [hβ, if_neg hc]
      obtain ⟨hp, hlo, -⟩ := hPmem n hnP
      exact isRough_of_prime _ n hp (lt_trans hC4 hlo)
    have := typeII_block M c u Ψ x a γ A (b / 2) (1 / 2 + κ / 2) (1 - b / 2) hT k l β hβ1 hβr
      h1 h2 h3 h4 h5 h6
    refine le_trans this ?_
    apply mul_le_mul_of_nonneg_right _ hL6
    calc A * (2 ^ l * 2 ^ k) ≤ max A 0 * (2 ^ l * 2 ^ k) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max A 0 * (2 * x) := mul_le_mul_of_nonneg_left h4 (le_max_right _ _)
  · push_neg at hex
    rw [Finset.sum_eq_zero, abs_zero]
    · exact mul_nonneg (mul_nonneg (le_max_right _ _) (by linarith)) hL6
    intro m hm
    apply Finset.sum_eq_zero
    intro n hn
    by_cases hnP : n ∈ P
    · have := hex m hm n hn (by simp only [hβ, if_pos hnP]; norm_num)
      rw [this]; ring
    · rw [if_neg hnP]; ring

open Classical in
/-- The Type II replacement in the bins (§12.4): `T_{γ,γ'}` minus its proxy is
`≪ L^2 · x L^{-6}`. -/
lemma bin_error (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (κ b γ γ' A : ℝ) (hκ : 0 < κ) (hb : 0 < b) (hbγ : b ≤ γ)
    (hγγ' : γ < γ') (hγ' : γ' ≤ 1 / 2 - κ)
    (hT : ∀ Hm Hn : ℝ, x ^ (b / 2) ≤ Hm → x ^ (b / 2) ≤ Hn → 1 / 4 * x ≤ Hm * Hn →
      Hm * Hn ≤ 2 * x →
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc Hm (2 * Hm) →
      1 / 2 + κ / 2 ≤ log Hm / log x → log (2 * Hm) / log x ≤ 1 - b / 2 →
      ∀ β : ℕ → ℂ, (∀ n, ‖β n‖ ≤ 1) →
        (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
      ‖∑ m ∈ (Finset.range (⌊2 * Hm⌋₊ + 1)).filter (fun m : ℕ => (m : ℝ) ∈ J),
          ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
          ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) * β n *
            (constructionWeight M c u Ψ x a (m * n) : ℂ)‖ ≤ A * (Hm * Hn) * log x ^ (-6 : ℝ))
    (hx : 1 < x) (hC1 : 2 * x ^ (b / 2) ≤ x ^ γ) (hC2 : log 2 ≤ κ / 2 * log x)
    (hC3 : log 4 ≤ b / 2 * log x) (hC4 : sieveLevel x < x ^ γ) :
    |∑ n ∈ (Finset.range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n),
        ∑' m : ℕ, (if IsRough (x ^ γ) m then constructionWeight M c u Ψ x a (m * n) else 0) -
      ∑ n ∈ (Finset.range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n),
        ∑' m : ℕ, roughProxy x γ m * constructionWeight M c u Ψ x a (m * n)| ≤
      ((Nat.log 2 ⌈2 * x⌉₊ + 1 : ℕ) : ℝ) ^ 2 * (max A 0 * (2 * x) * log x ^ (-6 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  set P := (Finset.range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n) with hP
  set w := constructionWeight M c u Ψ x a with hw
  set N := ⌈2 * x⌉₊ with hN
  set Lm := Nat.log 2 N + 1 with hLm
  have hNLm : N < 2 ^ Lm := Nat.lt_pow_succ_log_self (by norm_num) N
  have hPmem : ∀ n ∈ P, n.Prime ∧ x ^ γ < n ∧ (n : ℝ) ≤ x ^ γ' := by
    intro n hn
    simp only [hP, Finset.mem_filter, Finset.mem_range] at hn
    refine ⟨hn.2.1, hn.2.2, ?_⟩
    have := Nat.le_of_lt_succ hn.1
    exact le_trans (by exact_mod_cast this) (Nat.floor_le (by positivity))
  have hwz : ∀ m n, 1 ≤ n → N ≤ m → w (m * n) = 0 := fun m n hn hm =>
    weight_eq_zero_of_ge M c u Ψ hΨs x hx0 a _ (le_trans hm (Nat.le_mul_of_pos_right m hn))
  have hw0 : w 0 = 0 := weight_zero M c u Ψ x a
  have hstep : ∀ n ∈ P,
      ∑' m : ℕ, (if IsRough (x ^ γ) m then w (m * n) else 0) -
        ∑' m : ℕ, roughProxy x γ m * w (m * n) =
      ∑ m ∈ Finset.Ico 1 (2 ^ Lm), (roughIndicator x γ m - roughProxy x γ m) * w (m * n) := by
    intro n hn
    have hn1 : 1 ≤ n := (hPmem n hn).1.one_le
    have hz : ∀ m ∉ Finset.range (2 ^ Lm), ∀ f : ℕ → ℝ, f m * w (m * n) = 0 := by
      intro m hm f
      simp only [Finset.mem_range, not_lt] at hm
      rw [hwz m n hn1 (by omega), mul_zero]
    have e1 : ∑' m : ℕ, (if IsRough (x ^ γ) m then w (m * n) else 0) =
        ∑' m : ℕ, roughIndicator x γ m * w (m * n) := by
      apply tsum_congr; intro m; unfold roughIndicator; split_ifs <;> simp
    rw [e1, tsum_eq_sum (s := Finset.range (2 ^ Lm)) (fun m hm => hz m hm _),
      tsum_eq_sum (s := Finset.range (2 ^ Lm)) (fun m hm => hz m hm _), ← Finset.sum_sub_distrib,
      Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by positivity)]
    simp only [zero_mul, hw0, mul_zero, sub_zero, zero_add, sub_mul]
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl hstep]
  have hPsub : P ⊆ Finset.Ico 1 (2 ^ Lm) := by
    intro n hn
    obtain ⟨hp, -, hle⟩ := hPmem n hn
    rw [Finset.mem_Ico]
    refine ⟨hp.one_le, ?_⟩
    have h1 : x ^ γ' ≤ x := by
      calc x ^ γ' ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
        _ = x := Real.rpow_one x
    have h2 : (n : ℝ) < N := by
      have := Nat.le_ceil (2 * x); linarith
    have : n < N := by exact_mod_cast h2
    omega
  have hstepb : ∑ n ∈ P, ∑ m ∈ Finset.Ico 1 (2 ^ Lm),
        (roughIndicator x γ m - roughProxy x γ m) * w (m * n) =
      ∑ n ∈ Finset.Ico 1 (2 ^ Lm), ∑ m ∈ Finset.Ico 1 (2 ^ Lm),
        (roughIndicator x γ m - roughProxy x γ m) * (if n ∈ P then 1 else 0) * w (m * n) := by
    rw [← Finset.sum_subset hPsub]
    · apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m _
      rw [if_pos hn]; ring
    · intro n _ hn
      apply Finset.sum_eq_zero
      intro m _
      rw [if_neg hn]; ring
  rw [hstepb, block_decomp]
  calc _ ≤ ∑ k ∈ Finset.range Lm, ∑ l ∈ Finset.range Lm,
        |∑ m ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
          (roughIndicator x γ m - roughProxy x γ m) * (if n ∈ P then 1 else 0) * w (m * n)| :=
        le_trans (Finset.abs_sum_le_sum_abs _ _)
          (Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ k ∈ Finset.range Lm, ∑ l ∈ Finset.range Lm, max A 0 * (2 * x) * log x ^ (-6 : ℝ) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
          bin_block M c u Ψ hΨs x a κ b γ γ' A hκ hb hbγ hγγ' hγ' hT hx hC1 hC2 hC3 hC4 P
            hPmem k l
    _ = (Lm : ℝ) ^ 2 * (max A 0 * (2 * x) * log x ^ (-6 : ℝ)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

open Classical in
/-- The proxy sum in a bin, bounded by the conditioned masses (§12.4). -/
lemma bin_proxy (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (γ γ' S' : ℝ) (hx : 1 < x)
    (hC4 : sieveLevel x < x ^ γ)
    (hD : ∀ s, 1 - γ' < s → s < 1 - γ + log 2 / log x → roughDensity γ s ≤ S') :
    ∑ n ∈ (Finset.range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n),
        ∑' m : ℕ, roughProxy x γ m * constructionWeight M c u Ψ x a (m * n) ≤
      S' / (log x * mertensProduct (sieveLevel x)) *
        ∑ n ∈ (Finset.range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n),
          ∑' d : ℕ, (if n ∣ d ∧ IsRough (sieveLevel x) d then
            constructionWeight M c u Ψ x a d else 0) := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < log x := Real.log_pos hx
  have hV := mertensProduct_pos (sieveLevel x)
  have hLV : 0 < log x * mertensProduct (sieveLevel x) := mul_pos hL hV
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  have hnp := hn.2.1
  have hnlo := hn.2.2
  have hnhi : (n : ℝ) ≤ x ^ γ' :=
    le_trans (by exact_mod_cast Nat.le_of_lt_succ hn.1) (Nat.floor_le (by positivity))
  rw [← tsum_rough_mul_eq M c u Ψ x a (sieveLevel x) n hnp (lt_trans hC4 hnlo),
    ← tsum_mul_left]
  have hsum1 : Summable (fun m : ℕ => roughProxy x γ m * constructionWeight M c u Ψ x a (m * n)) := by
    apply summable_of_ne_finset_zero (s := Finset.range ⌈2 * x⌉₊)
    intro m hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [weight_eq_zero_of_ge M c u Ψ hΨs x hx0 a _
      (le_trans hm (Nat.le_mul_of_pos_right m hnp.pos)), mul_zero]
  have hsum2 : Summable (fun m : ℕ => S' / (log x * mertensProduct (sieveLevel x)) *
      (if IsRough (sieveLevel x) m then constructionWeight M c u Ψ x a (m * n) else 0)) := by
    apply summable_of_ne_finset_zero (s := Finset.range ⌈2 * x⌉₊)
    intro m hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [weight_eq_zero_of_ge M c u Ψ hΨs x hx0 a _
      (le_trans hm (Nat.le_mul_of_pos_right m hnp.pos))]
    simp
  refine Summable.tsum_le_tsum (fun m => ?_) hsum1 hsum2
  unfold roughProxy
  by_cases hr : IsRough (sieveLevel x) m
  swap
  · simp only [hr, if_false, mul_zero, zero_mul, le_refl]
  simp only [hr, if_true, mul_one]
  by_cases hwz : constructionWeight M c u Ψ x a (m * n) = 0
  · rw [hwz]; simp
  have hw0 : 0 ≤ constructionWeight M c u Ψ x a (m * n) := constructionWeight_nonneg M c u Ψ hΨ0 x a _
  obtain ⟨-, -, hxmn, hmn2x, -⟩ := constructionWeight_support M c u Ψ hΨs x hx0 a _ hwz
  push_cast at hxmn hmn2x
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnp.pos
  have hm0 : (0 : ℝ) < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hxmn; simp at hxmn; linarith
    · exact_mod_cast h0
  have hlogn : log n ≤ γ' * log x := by
    have := Real.log_le_log hn0 hnhi
    rwa [Real.log_rpow hx0] at this
  have hlogn' : γ * log x < log n := by
    have := Real.log_lt_log (by positivity) hnlo
    rwa [Real.log_rpow hx0] at this
  have hlogmn : log x < log m + log n := by
    rw [← Real.log_mul hm0.ne' hn0.ne']; exact Real.log_lt_log hx0 hxmn
  have hlogmn2 : log m + log n < log 2 + log x := by
    rw [← Real.log_mul hm0.ne' hn0.ne', ← Real.log_mul (by norm_num) hx0.ne']
    exact Real.log_lt_log (by positivity) hmn2x
  have hs1 : 1 - γ' < log m / log x := by
    rw [lt_div_iff₀ hL]; nlinarith
  have hs2 : log m / log x < 1 - γ + log 2 / log x := by
    rw [div_lt_iff₀ hL, add_mul, div_mul_cancel₀ _ hL.ne']; nlinarith
  have := hD _ hs1 hs2
  apply mul_le_mul_of_nonneg_right _ hw0
  exact div_le_div_of_nonneg_right this hLV.le

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

lemma final_arith (Sup lg η η₁ η₂ : ℝ) (hSup0 : 0 ≤ Sup) (hlg : 0 < lg) (hη : 0 < η)
    (hη₁0 : 0 ≤ η₁) (hη₁1 : η₁ ≤ 1) (hη₁le : η₁ ≤ η / (4 * (lg + 1)))
    (hη₂ : η₂ = η / (4 * (Sup + 1))) :
    (Sup + η₁) * (lg + η₂) + η / 4 ≤ Sup * lg + η := by
  have hη₁lg : η₁ * lg ≤ η / 4 := by
    calc η₁ * lg ≤ η / (4 * (lg + 1)) * lg := mul_le_mul_of_nonneg_right hη₁le hlg.le
      _ ≤ η / 4 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have hη₂0 : 0 ≤ η₂ := by rw [hη₂]; positivity
  have hSη₂ : Sup * η₂ ≤ η / 4 := by
    rw [hη₂, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hη₂le : η₂ ≤ η / 4 := by
    rw [hη₂, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have : η₁ * η₂ ≤ η₂ := by nlinarith
  nlinarith

set_option maxHeartbeats 1000000 in
open Classical in
/-- The bin cost (12.24). -/
theorem bin_cost (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y)
    (κ b γ γ' : ℝ) (hκ : 0 < κ) (hκ' : κ < 0.01) (hb : 0 < b) (hb' : b < 0.01)
    (hbγ : b ≤ γ) (hγγ' : γ < γ') (hγ' : γ' ≤ 1 / 2 - κ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        ∑ n ∈ (Finset.range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n),
            ∑' m : ℕ, (if IsRough (x ^ γ) m then constructionWeight M c u Ψ x a (m * n) else 0)
          ≤ singularSeries M * totalMass M c u Ψ x a / log x *
            (sSup ((fun t => roughDensity γ (1 - t)) '' Set.Icc γ γ') * log (γ' / γ) + η) := by
  have hγ0 : 0 < γ := lt_of_lt_of_le hb hbγ
  obtain ⟨K₀, hK₀⟩ := type_ii_progression M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi
    (b / 2) γ (1 / 2 + κ / 2) (1 - b / 2) (by positivity) hγ0 (by linarith) (by linarith)
    (by linarith) (1 / 4) 2 (by norm_num)
  refine ⟨K₀, fun K hK1 hKK a ha ha' η hη => ?_⟩
  obtain ⟨A, x₁, hA⟩ := hK₀ K hK1 hKK a ha ha'
  -- the supremum of the density on the bin
  set f : ℝ → ℝ := fun t => roughDensity γ (1 - t) with hf
  set Sup := sSup (f '' Set.Icc γ γ') with hSup
  have hfcont : ContinuousOn f (Set.Icc γ γ') := by
    apply roughDensity_continuousOn.comp
      (continuous_const.prodMk (continuous_const.sub continuous_id)).continuousOn
    intro t ht
    show 0 < γ ∧ 0 < 1 - t
    constructor <;> linarith [ht.2]
  have hbdd : BddAbove (f '' Set.Icc γ γ') := isCompact_Icc.bddAbove_image hfcont
  have hγmem : γ ∈ Set.Icc γ γ' := ⟨le_rfl, hγγ'.le⟩
  have hfγ : f γ ≤ Sup := le_csSup hbdd ⟨γ, hγmem, rfl⟩
  have hSup0 : 0 ≤ Sup :=
    le_trans (roughDensity_nonneg γ (1 - γ) hγ0 (by linarith)) hfγ
  set lg := log (γ' / γ) with hlg
  have hlg0 : 0 < lg := Real.log_pos (by rw [lt_div_iff₀ hγ0]; linarith)
  set η₁ := min 1 (η / (4 * (lg + 1))) with hη₁
  have hη₁0 : 0 < η₁ := lt_min one_pos (by positivity)
  set η₂ := η / (4 * (Sup + 1)) with hη₂
  have hη₂0 : 0 < η₂ := by positivity
  -- continuity of `D_γ` at `1 - γ`
  have hcont : ContinuousAt (fun s => roughDensity γ s) (1 - γ) := by
    have h1 : ContinuousOn (fun s => roughDensity γ s) (Set.Ioi 0) := by
      apply roughDensity_continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      intro s hs
      exact ⟨hγ0, hs⟩
    exact h1.continuousAt (Ioi_mem_nhds (by linarith))
  obtain ⟨ρ, hρ, hρD⟩ := Metric.continuousAt_iff.mp hcont η₁ hη₁0
  have hD : ∀ s, 1 - γ' < s → s < 1 - γ + ρ → roughDensity γ s ≤ Sup + η₁ := by
    intro s hs1 hs2
    by_cases hs : s ≤ 1 - γ
    · have : f (1 - s) ≤ Sup := le_csSup hbdd ⟨1 - s, ⟨by linarith, by linarith⟩, rfl⟩
      simp only [hf, sub_sub_cancel] at this
      linarith
    · push_neg at hs
      have := hρD (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rw [Real.dist_eq, abs_lt] at this
      simp only [hf] at hfγ
      linarith [this.2]
  -- the conditioned mass (Lemma 12.4)
  obtain ⟨x₂, hx₂⟩ := mass_conditioned_on_divisor M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi
    K hK1 a ha ha' κ b hκ hκ' hb hb' γ γ' hbγ hγγ' hγ' η₂ hη₂0
  -- the size of the total mass
  obtain ⟨-, c₁, c₂, hc₁, hc₂, hwfd⟩ :=
    weighted_family_distribution M hM h8 Ψ hΨ hΨs hΨ0 hΨ1 hΨi
  obtain ⟨x₃, hx₃⟩ := hwfd c u hc hu hcu hcop K hK1 a ha ha'
  obtain ⟨CJ, hCJ⟩ := harmonic_mass M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi K hK1
  obtain ⟨x₄, hx₄⟩ := hCJ a ha ha' 1 one_pos
  have hS := singularSeries_pos M
  set L₀ : ℝ := max (max (log 2 / ρ + 1) (2 * log 2 / κ)) (max (2 * log 4 / b)
    (max 5 (8 * max A 0 / (η / 4 * singularSeries M * c₁)))) with hL₀
  have hev : ∀ᶠ x : ℝ in atTop, L₀ ≤ log x ∧ sieveLevel x < x ^ γ ∧
      x₁ ≤ x ∧ x₂ ≤ x ∧ x₃ ≤ x ∧ x₄ ≤ x ∧ 1 < x :=
    (Real.tendsto_log_atTop.eventually_ge_atTop L₀).and ((eventually_sieveLevel_lt γ hγ0).and
      ((eventually_ge_atTop x₁).and ((eventually_ge_atTop x₂).and ((eventually_ge_atTop x₃).and
        ((eventually_ge_atTop x₄).and (eventually_gt_atTop 1))))))
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨hLx, hC4, hx1, hx2, hx3, hx4, hx1'⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hL : 0 < log x := Real.log_pos hx1'
  have hL5 : 5 ≤ log x := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hLx
  have hLρ : log 2 / ρ + 1 ≤ log x :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLx
  have hLκ : 2 * log 2 / κ ≤ log x :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLx
  have hLb : 2 * log 4 / b ≤ log x :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLx
  have hLA : 8 * max A 0 / (η / 4 * singularSeries M * c₁) ≤ log x :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hLx
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hC2 : log 2 ≤ κ / 2 * log x := by
    rw [div_le_iff₀ hκ] at hLκ; linarith
  have hC3 : log 4 ≤ b / 2 * log x := by
    rw [div_le_iff₀ hb] at hLb; linarith
  have hC1 : 2 * x ^ (b / 2) ≤ x ^ γ := by
    have h2 : 2 ≤ x ^ (b / 2) := by
      rw [Real.rpow_def_of_pos hx0]
      have : log 2 ≤ log x * (b / 2) := by
        have : log 4 = 2 * log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        nlinarith
      calc (2 : ℝ) = exp (log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ exp (log x * (b / 2)) := Real.exp_le_exp.mpr this
    have h3 : x ^ (b / 2) * x ^ (b / 2) ≤ x ^ γ := by
      rw [← Real.rpow_add hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)
    have : 0 < x ^ (b / 2) := by positivity
    nlinarith
  have hρL : log 2 / log x < ρ := by
    rw [div_lt_iff₀ hL]
    have : log 2 / ρ < log x := by linarith
    rw [div_lt_iff₀ hρ] at this; linarith
  -- the Type II error
  have herr := bin_error M c u Ψ hΨs x a κ b γ γ' A hκ hb hbγ hγγ' hγ'
    (fun Hm Hn h1 h2 h3 h4 J hJ hJs h5 h6 β hβ1 hβs =>
      hA x hx1 Hm Hn h1 h2 h3 h4 J hJ hJs h5 h6 β hβ1 hβs) hx1' hC1 hC2 hC3 hC4
  -- the proxy sum
  have hprox := bin_proxy M c u Ψ hΨs hΨ0 x a γ γ' (Sup + η₁) hx1' hC4
    (fun s hs1 hs2 => hD s hs1 (by linarith))
  have hcond := hx₂ x hx2
  set X₀ := totalMass M c u Ψ x a with hX₀
  have hX0 : 0 ≤ X₀ := totalMass_nonneg M c u Ψ hΨ0 x a
  set V := mertensProduct (sieveLevel x) with hV
  have hVpos : 0 < V := mertensProduct_pos _
  set T := ∑ n ∈ (Finset.range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n),
      ∑' m : ℕ, (if IsRough (x ^ γ) m then constructionWeight M c u Ψ x a (m * n) else 0)
  set T' := ∑ n ∈ (Finset.range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n),
      ∑' m : ℕ, roughProxy x γ m * constructionWeight M c u Ψ x a (m * n)
  set Sc := ∑ n ∈ (Finset.range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n),
      ∑' d : ℕ, (if n ∣ d ∧ IsRough (sieveLevel x) d then
        constructionWeight M c u Ψ x a d else 0)
  have hSc : Sc ≤ singularSeries M * X₀ * V * (lg + η₂) := by
    have := (abs_le.mp hcond).2
    have e : singularSeries M * X₀ * V * (lg + η₂) =
        singularSeries M * X₀ * V * lg + η₂ * (singularSeries M * X₀ * V) := by ring
    linarith
  have hT' : T' ≤ singularSeries M * X₀ / log x * ((Sup + η₁) * (lg + η₂)) := by
    refine le_trans hprox ?_
    calc (Sup + η₁) / (log x * V) * Sc
        ≤ (Sup + η₁) / (log x * V) * (singularSeries M * X₀ * V * (lg + η₂)) :=
          mul_le_mul_of_nonneg_left hSc (by positivity)
      _ = singularSeries M * X₀ / log x * ((Sup + η₁) * (lg + η₂)) := by
          field_simp
  -- the error is small
  have hLm := natLog_bound x hx1'.le
  have hLm2 : ((Nat.log 2 ⌈2 * x⌉₊ + 1 : ℕ) : ℝ) ≤ 2 * log x := by
    have hl3 : log 3 < 1.2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      have h2 := Real.log_two_lt_d9
      have : log 3 = log 2 + log (3 / 2) := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
      have h32 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
      linarith
    have hl2 := Real.log_two_gt_d9
    have hpos : (0 : ℝ) ≤ ((Nat.log 2 ⌈2 * x⌉₊ + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hJ := (hx₄ x hx4).2.2.1
  have hXlow := (hx₃ x hx3).1
  have hsmall := typeII_error_small x (log x) (max A 0) _ (η / 4) (singularSeries M) c₁ X₀
    (harmonicMass x a) (by linarith) hx0 (le_max_right _ _) (Nat.cast_nonneg _) hLm2
    (by positivity) hS hc₁ hJ hXlow hLA
  have hTT : T ≤ T' + η / 4 * (singularSeries M * X₀ / log x) := by
    have := (abs_le.mp (le_trans herr hsmall)).2
    linarith
  -- final arithmetic
  have hA0 : 0 ≤ singularSeries M * X₀ / log x := by positivity
  have hprod := final_arith Sup lg η η₁ η₂ hSup0 hlg0 hη hη₁0.le (min_le_left _ _)
    (min_le_right _ _) hη₂
  calc T ≤ T' + η / 4 * (singularSeries M * X₀ / log x) := hTT
    _ ≤ singularSeries M * X₀ / log x * ((Sup + η₁) * (lg + η₂)) +
          η / 4 * (singularSeries M * X₀ / log x) := by linarith
    _ = singularSeries M * X₀ / log x * ((Sup + η₁) * (lg + η₂) + η / 4) := by ring
    _ ≤ singularSeries M * X₀ / log x * (Sup * lg + η) :=
        mul_le_mul_of_nonneg_left hprod hA0

end ArtinPrimitiveRoots.P21bin_cost

open ArtinPrimitiveRoots ArtinPrimitiveRoots.P21bin_cost Real in
open Classical in
theorem solution (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y)
    (κ b γ γ' : ℝ) (hκ : 0 < κ) (hκ' : κ < 0.01) (hb : 0 < b) (hb' : b < 0.01)
    (hbγ : b ≤ γ) (hγγ' : γ < γ') (hγ' : γ' ≤ 1 / 2 - κ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        ∑ n ∈ (Finset.range (⌊x ^ γ'⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ < n),
            ∑' m : ℕ, (if IsRough (x ^ γ) m then constructionWeight M c u Ψ x a (m * n) else 0)
          ≤ singularSeries M * totalMass M c u Ψ x a / log x *
            (sSup ((fun t => roughDensity γ (1 - t)) '' Set.Icc γ γ') * log (γ' / γ) + η) :=
  ArtinPrimitiveRoots.P21bin_cost.bin_cost M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi κ b γ γ' hκ hκ' hb hb' hbγ hγγ' hγ'
