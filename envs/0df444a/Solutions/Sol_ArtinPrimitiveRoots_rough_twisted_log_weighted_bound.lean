-- Prove2me | solution 1 for ArtinPrimitiveRoots.rough_twisted_log_weighted_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T13:52:14.612017+00:00
-- url     : https://prove2.me/submissions/aebc9bc8-c467-41e6-b02c-6ea4a78d199c

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_log_phase_progression
import Theorems.Thm_ArtinPrimitiveRoots_mertens_product

section
/-!
# Two partial-summation lemmas

* `layer_cake_sum`: if a coefficient sequence has partial sums `κ |J'| + O(ε)` on every
  subinterval `J'` of an interval `J`, then against a monotone weight `0 ≤ ψ ≤ Ψ` its sum over
  `J` is `κ ∫_J ψ + O(Ψ ε)`. Integrate the hypothesis over the level sets
  `{y ∈ J : s < ψ y}`, `0 < s ≤ Ψ`, and use the layer-cake formula.
* `abel_cpow`: discrete Abel summation against `j^{iu}`.
-/

namespace ArtinPrimitiveRoots.A106R

open Real MeasureTheory Set Filter

open Classical in
/-- Partial summation against a monotone weight, by the layer-cake formula. -/
theorem layer_cake_sum (S : Finset ℕ) {J : Set ℝ} (hJ : J.OrdConnected) {a b : ℝ}
    (hJab : J ⊆ Icc a b) {ψ : ℝ → ℝ} (hψ : MonotoneOn ψ (Icc a b)) {Ψ : ℝ} (hΨ : 0 ≤ Ψ)
    (hψ0 : ∀ y ∈ J, 0 ≤ ψ y) (hψΨ : ∀ y ∈ J, ψ y ≤ Ψ) (c : ℕ → ℂ) (κ : ℂ) (ε : ℝ)
    (hc : ∀ J' : Set ℝ, J'.OrdConnected → J' ⊆ J →
      ‖(∑ m ∈ S, if (m : ℝ) ∈ J' then c m else 0) - κ * ((volume J').toReal : ℂ)‖ ≤ ε) :
    ‖(∑ m ∈ S, if (m : ℝ) ∈ J then c m * (ψ m : ℂ) else 0) -
        κ * ((∫ y in J, ψ y : ℝ) : ℂ)‖ ≤ Ψ * ε := by
  classical
  set Js : ℝ → Set ℝ := fun s => {y | y ∈ J ∧ s < ψ y} with hJs_def
  have hJs_oc : ∀ s, (Js s).OrdConnected := fun s =>
    ⟨fun y₁ hy₁ y₂ hy₂ y hy =>
      ⟨hJ.out hy₁.1 hy₂.1 hy,
        lt_of_lt_of_le hy₁.2 (hψ (hJab hy₁.1) (hJab (hJ.out hy₁.1 hy₂.1 hy)) hy.1)⟩⟩
  have hJs_sub : ∀ s, Js s ⊆ J := fun s _ hy => hy.1
  have hJmeas : MeasurableSet J := hJ.measurableSet
  have hJfin : volume J < ⊤ :=
    lt_of_le_of_lt (measure_mono hJab) measure_Icc_lt_top
  -- the volume function
  set v : ℝ → ℝ := fun s => (volume (Js s)).toReal with hv_def
  have hv_anti : Antitone v := by
    intro s s' hss'
    refine ENNReal.toReal_mono (lt_of_le_of_lt (measure_mono (hJs_sub s)) hJfin).ne
      (measure_mono fun y hy => ⟨hy.1, lt_of_le_of_lt hss' hy.2⟩)
  have hv_bd : ∀ s, ‖v s‖ ≤ (volume J).toReal := by
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hJfin.ne (measure_mono (hJs_sub s))
  have hIoc_fin : volume (Ioc (0 : ℝ) Ψ) < ⊤ := measure_Ioc_lt_top
  have hv_int : IntegrableOn v (Ioc 0 Ψ) :=
    Measure.integrableOn_of_bounded (M := (volume J).toReal) hIoc_fin.ne
      hv_anti.measurable.aestronglyMeasurable (Eventually.of_forall hv_bd)
  -- the indicator functions
  set g : ℕ → ℝ → ℂ := fun m s =>
    if (m : ℝ) ∈ J then (Iio (ψ m)).indicator (fun _ => c m) s else 0 with hg_def
  have hg_int : ∀ m, IntegrableOn (g m) (Ioc 0 Ψ) := by
    intro m
    by_cases hm : (m : ℝ) ∈ J
    · simp only [hg_def, hm, if_true]
      exact (integrableOn_const hIoc_fin.ne).indicator measurableSet_Iio
    · simp only [hg_def, hm, if_false]
      exact integrableOn_zero
  have hg_val : ∀ m, ∫ s in Ioc 0 Ψ, g m s =
      if (m : ℝ) ∈ J then c m * (ψ m : ℂ) else 0 := by
    intro m
    by_cases hm : (m : ℝ) ∈ J
    · simp only [hg_def, hm, if_true]
      rw [setIntegral_indicator measurableSet_Iio, setIntegral_const]
      have hset : Ioc 0 Ψ ∩ Iio (ψ m) = Ioo 0 (ψ m) := by
        ext s
        simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, (h3.trans_le (hψΨ _ hm)).le⟩, h3⟩
      rw [hset, Real.volume_real_Ioo_of_le (hψ0 _ hm), sub_zero, Complex.real_smul, mul_comm]
    · simp [hg_def, hm]
  -- the level-set discrepancy
  have hF_bd : ∀ s ∈ Ioc (0 : ℝ) Ψ,
      ‖(∑ m ∈ S, g m s) - κ * ((v s : ℝ) : ℂ)‖ ≤ ε := by
    intro s _
    convert hc (Js s) (hJs_oc s) (hJs_sub s) using 3
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hJs_def, hg_def, mem_ofPred_eq, Set.indicator_apply, mem_Iio]
    by_cases hm : (m : ℝ) ∈ J <;> simp [hm]
  -- layer cake for the integral of ψ
  have hψint : IntegrableOn ψ J :=
    ((hψ.integrableOn_isCompact isCompact_Icc).mono_set hJab)
  have hψnn : 0 ≤ᵐ[volume.restrict J] ψ :=
    (ae_restrict_iff' hJmeas).2 (Eventually.of_forall hψ0)
  have hlayer : ∫ y in J, ψ y = ∫ s in Ioc 0 Ψ, v s := by
    rw [Integrable.integral_eq_integral_meas_lt hψint hψnn]
    have hcongr : ∀ s, (volume.restrict J).real {y | s < ψ y} = v s := by
      intro s
      simp only [Measure.real, Measure.restrict_apply' hJmeas, hv_def, hJs_def]
      congr 2
      ext y
      simp [and_comm]
    simp_rw [hcongr]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun s hs => hs.1) fun s hs => ?_
    have hs' : Ψ < s := by
      rcases hs with ⟨hs0, hs1⟩
      simp only [mem_Ioc, not_and, not_le] at hs1
      exact hs1 hs0
    have hempty : Js s = ∅ := by
      ext y
      simp only [hJs_def, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro hy
      exact (hψΨ y hy).trans hs'.le
    simp [hv_def, hempty]
  -- assemble
  have hkey : ∫ s in Ioc 0 Ψ, ((∑ m ∈ S, g m s) - κ * ((v s : ℝ) : ℂ)) =
      (∑ m ∈ S, if (m : ℝ) ∈ J then c m * (ψ m : ℂ) else 0) -
        κ * ((∫ y in J, ψ y : ℝ) : ℂ) := by
    have hi1 : Integrable (fun s => ∑ m ∈ S, g m s) (volume.restrict (Ioc 0 Ψ)) :=
      integrable_finsetSum S fun m _ => hg_int m
    have hi2 : Integrable (fun s => κ * ((v s : ℝ) : ℂ)) (volume.restrict (Ioc 0 Ψ)) :=
      (hv_int.ofReal).const_mul κ
    rw [integral_sub hi1 hi2, integral_finsetSum S fun m _ => hg_int m, integral_const_mul, integral_complex_ofReal,
      hlayer]
    exact congrArg (· - _) (Finset.sum_congr rfl fun m _ => hg_val m)
  rw [← hkey]
  calc ‖∫ s in Ioc 0 Ψ, ((∑ m ∈ S, g m s) - κ * ((v s : ℝ) : ℂ))‖
      ≤ ε * volume.real (Ioc (0 : ℝ) Ψ) := norm_setIntegral_le_of_norm_le_const hIoc_fin hF_bd
    _ = Ψ * ε := by rw [Real.volume_real_Ioc_of_le hΨ, sub_zero, mul_comm]

end ArtinPrimitiveRoots.A106R
end

section
/-! # Shared tools for prover S (A106): Bonferroni truncation, residue counts, Abel summation -/

namespace ArtinPrimitiveRoots.A106S

open Real Finset

/-! ## Bonferroni truncation -/

/-- The alternating sum `Σ_{S ⊆ P, |S| < n} (-1)^{|S|} ∏_{p ∈ S} a p`. -/
noncomputable def bonfTrunc (P : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ S ∈ P.powerset, if S.card < n then (-1 : ℝ) ^ S.card * ∏ p ∈ S, a p else 0

/-- The elementary symmetric sum `e_n(a) = Σ_{S ⊆ P, |S| = n} ∏_{p ∈ S} a p`. -/
noncomputable def esym (P : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ S ∈ P.powerset, if S.card = n then ∏ p ∈ S, a p else 0

lemma bonfTrunc_zero (P : Finset ℕ) (a : ℕ → ℝ) : bonfTrunc P a 0 = 0 := by
  simp [bonfTrunc]

lemma esym_zero (P : Finset ℕ) (a : ℕ → ℝ) : esym P a 0 = 1 := by
  unfold esym
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro S _ hS; simp [Finset.card_eq_zero, hS]
  · intro h; exact absurd (Finset.empty_mem_powerset P) h

lemma bonfTrunc_insert (P : Finset ℕ) (a : ℕ → ℝ) (q : ℕ) (hq : q ∉ P) (n : ℕ) :
    bonfTrunc (insert q P) a (n + 1) = bonfTrunc P a (n + 1) - a q * bonfTrunc P a n := by
  unfold bonfTrunc
  rw [Finset.sum_powerset_insert hq, sub_eq_add_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun S hS => ?_
  have hqS : q ∉ S := fun h => hq (Finset.mem_powerset.1 hS h)
  rw [Finset.card_insert_of_notMem hqS, Finset.prod_insert hqS]
  by_cases h : S.card < n
  · rw [if_pos (by omega), if_pos h]; ring
  · rw [if_neg (by omega), if_neg h]; ring

lemma esym_insert (P : Finset ℕ) (a : ℕ → ℝ) (q : ℕ) (hq : q ∉ P) (n : ℕ) :
    esym (insert q P) a (n + 1) = esym P a (n + 1) + a q * esym P a n := by
  unfold esym
  rw [Finset.sum_powerset_insert hq, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun S hS => ?_
  have hqS : q ∉ S := fun h => hq (Finset.mem_powerset.1 hS h)
  rw [Finset.card_insert_of_notMem hqS, Finset.prod_insert hqS]
  by_cases h : S.card = n
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]; ring

lemma bonf_signed (a : ℕ → ℝ) (P : Finset ℕ) (ha : ∀ p ∈ P, 0 ≤ a p ∧ a p ≤ 1) :
    ∀ n : ℕ, 0 ≤ (-1 : ℝ) ^ n * (∏ p ∈ P, (1 - a p) - bonfTrunc P a n) ∧
      (-1 : ℝ) ^ n * (∏ p ∈ P, (1 - a p) - bonfTrunc P a n) ≤ esym P a n := by
  induction P using Finset.induction_on with
  | empty => intro n; cases n <;> simp [bonfTrunc, esym]
  | insert q P hq ih =>
    have ha' : ∀ p ∈ P, 0 ≤ a p ∧ a p ≤ 1 := fun p hp => ha p (Finset.mem_insert_of_mem hp)
    have haq := ha q (Finset.mem_insert_self q P)
    intro n
    cases n with
    | zero =>
      simp only [pow_zero, one_mul, bonfTrunc_zero, sub_zero, esym_zero]
      refine ⟨Finset.prod_nonneg fun p hp => by linarith [(ha p hp).2],
        Finset.prod_le_one (fun p hp => by linarith [(ha p hp).2])
          (fun p hp => by linarith [(ha p hp).1])⟩
    | succ n =>
      obtain ⟨h1, h2⟩ := ih ha' (n + 1)
      obtain ⟨h3, h4⟩ := ih ha' n
      rw [bonfTrunc_insert P a q hq, esym_insert P a q hq, Finset.prod_insert hq]
      have e : (-1 : ℝ) ^ (n + 1) * ((1 - a q) * ∏ p ∈ P, (1 - a p) -
          (bonfTrunc P a (n + 1) - a q * bonfTrunc P a n)) =
          (-1 : ℝ) ^ (n + 1) * (∏ p ∈ P, (1 - a p) - bonfTrunc P a (n + 1)) +
            a q * ((-1 : ℝ) ^ n * (∏ p ∈ P, (1 - a p) - bonfTrunc P a n)) := by
        rw [pow_succ]; ring
      rw [e]
      constructor
      · have := mul_nonneg haq.1 h3; linarith
      · have := mul_le_mul_of_nonneg_left h4 haq.1; linarith

/-- Bonferroni's inequalities: the truncation error is at most the next elementary symmetric
sum. -/
lemma bonferroni (a : ℕ → ℝ) (P : Finset ℕ) (ha : ∀ p ∈ P, 0 ≤ a p ∧ a p ≤ 1) (n : ℕ) :
    |∏ p ∈ P, (1 - a p) - bonfTrunc P a n| ≤ esym P a n := by
  obtain ⟨h1, h2⟩ := bonf_signed a P ha n
  have : |∏ p ∈ P, (1 - a p) - bonfTrunc P a n| =
      (-1 : ℝ) ^ n * (∏ p ∈ P, (1 - a p) - bonfTrunc P a n) := by
    rw [← abs_of_nonneg h1, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [this]; exact h2

lemma pow_succ_add_le (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (n : ℕ) :
    s ^ (n + 1) + (n + 1) * a * s ^ n ≤ (s + a) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 : 0 ≤ s ^ n := pow_nonneg hs n
    have h1 : 0 ≤ (n + 1 : ℝ) * a * a * s ^ n := by positivity
    calc s ^ (n + 1 + 1) + ((n + 1 : ℕ) + 1 : ℝ) * a * s ^ (n + 1)
        ≤ (s + a) * (s ^ (n + 1) + (n + 1) * a * s ^ n) := by
          push_cast; rw [pow_succ, pow_succ]; nlinarith
      _ ≤ (s + a) * (s + a) ^ (n + 1) := mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (s + a) ^ (n + 1 + 1) := by rw [pow_succ]; ring

/-! ## Residue classes in intervals -/

/-! ## Abel summation over tails -/

/-! ## Exponential sums over progressions -/

lemma norm_cpow_I_mul_sub (y t u : ℝ) (hy : 0 < y) (ht : 0 < t) :
    ‖(y : ℂ) ^ (Complex.I * u) - (t : ℂ) ^ (Complex.I * u)‖ ≤ |u| * |log y - log t| := by
  have ey : (y : ℂ) ^ (Complex.I * u) = Complex.exp (Complex.I * ((u * log y : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'), ← Complex.ofReal_log hy.le]
    push_cast; ring_nf
  have et : (t : ℂ) ^ (Complex.I * u) = Complex.exp (Complex.I * ((u * log t : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ht.ne'), ← Complex.ofReal_log ht.le]
    push_cast; ring_nf
  rw [ey, et]
  have : Complex.exp (Complex.I * ((u * log y : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((u * log t : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((u * log t : ℝ) : ℂ)) *
        (Complex.exp (Complex.I * ((u * log y - u * log t : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; push_cast; ring_nf
  rw [this, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, ← mul_sub, abs_mul]

/-- One step of the telescoping comparison: `F(t+k) - F(t) - k t^{iu}` is small, where
`F(y) = y^{1+iu}/(1+iu)`. -/
lemma step_bound (u t k : ℝ) (ht : 0 < t) (hk : 0 ≤ k) :
    ‖((t + k : ℝ) : ℂ) ^ (Complex.I * u + 1) / (Complex.I * u + 1) -
        (t : ℂ) ^ (Complex.I * u + 1) / (Complex.I * u + 1) -
        (k : ℂ) * (t : ℂ) ^ (Complex.I * u)‖ ≤ |u| * k / t * k := by
  set r : ℂ := Complex.I * u
  have hr : r ≠ -1 := by
    intro h
    have := congrArg Complex.re h
    simp [r] at this
  let G : ℝ → ℂ := fun y => (y : ℂ) ^ (r + 1) / (r + 1) - (y : ℂ) * (t : ℂ) ^ r
  have hG : ∀ y ∈ Set.Icc t (t + k), HasDerivWithinAt G ((y : ℂ) ^ r - (t : ℂ) ^ r)
      (Set.Icc t (t + k)) y := by
    intro y hy
    have hy0 : y ≠ 0 := by linarith [hy.1]
    have h1 := hasDerivAt_ofReal_cpow_const' hy0 hr
    have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * (t : ℂ) ^ r) (1 * (t : ℂ) ^ r) y :=
      (hasDerivAt_id y).ofReal_comp.mul_const _
    rw [one_mul] at h2
    exact (h1.sub h2).hasDerivWithinAt
  have hbd : ∀ y ∈ Set.Ico t (t + k), ‖(y : ℂ) ^ r - (t : ℂ) ^ r‖ ≤ |u| * k / t := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    refine (norm_cpow_I_mul_sub y t u hy0 ht).trans ?_
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg u)
    have hl : log t ≤ log y := log_le_log ht hy.1
    rw [abs_of_nonneg (by linarith)]
    have : log y - log t = log (y / t) := (log_div hy0.ne' ht.ne').symm
    rw [this]
    refine (log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one ht.ne']
    exact div_le_div_of_nonneg_right (by linarith [hy.2]) ht.le
  have := norm_image_sub_le_of_norm_deriv_le_segment' hG hbd (t + k) ⟨by linarith, le_refl _⟩
  simp only [G] at this
  rw [show t + k - t = k by ring] at this
  have e : ((t + k : ℝ) : ℂ) ^ (r + 1) / (r + 1) - (t : ℂ) ^ (r + 1) / (r + 1) -
      (k : ℂ) * (t : ℂ) ^ r = ((t + k : ℝ) : ℂ) ^ (r + 1) / (r + 1) - ((t + k : ℝ) : ℂ) * (t : ℂ) ^ r -
      ((t : ℂ) ^ (r + 1) / (r + 1) - (t : ℂ) * (t : ℂ) ^ r) := by
    push_cast; ring
  rw [e]; exact this

lemma norm_F_le (u y : ℝ) (hy : 0 < y) (hu : u ≠ 0) :
    ‖(y : ℂ) ^ (Complex.I * u + 1) / (Complex.I * u + 1)‖ ≤ y / |u| := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hre : (Complex.I * u + 1).re = 1 := by simp
  rw [hre, rpow_one]
  have h1 : |u| ≤ ‖Complex.I * u + 1‖ := by
    have := Complex.abs_im_le_norm (Complex.I * u + 1)
    simpa using this
  exact div_le_div_of_nonneg_left hy.le (abs_pos.2 hu) h1

lemma ap_sum_telescope (u : ℝ) (hu : u ≠ 0) (t₀ k : ℝ) (ht₀ : 0 < t₀) (hk : 0 < k) (c : ℕ) :
    ‖∑ j ∈ range c, (((t₀ + k * j : ℝ)) : ℂ) ^ (Complex.I * u)‖ ≤
      ((t₀ + k * c) + t₀) / (k * |u|) + ∑ j ∈ range c, k * |u| / (t₀ + k * j) := by
  set r : ℂ := Complex.I * u
  let F : ℝ → ℂ := fun y => (y : ℂ) ^ (r + 1) / (r + 1)
  have hstep : ∀ j ∈ range c, ‖F (t₀ + k * (j + 1 : ℕ)) - F (t₀ + k * j) -
      (k : ℂ) * ((t₀ + k * j : ℝ) : ℂ) ^ r‖ ≤ |u| * k / (t₀ + k * j) * k := by
    intro j _
    have hpos : 0 < t₀ + k * j := by positivity
    have := step_bound u (t₀ + k * j) k hpos hk.le
    simp only [F]
    rw [show t₀ + k * ((j + 1 : ℕ) : ℝ) = t₀ + k * j + k by push_cast; ring]
    exact this
  have htel : ∑ j ∈ range c, (F (t₀ + k * (j + 1 : ℕ)) - F (t₀ + k * j)) =
      F (t₀ + k * c) - F (t₀ + k * (0 : ℕ)) :=
    Finset.sum_range_sub (fun j : ℕ => F (t₀ + k * j)) c
  have hsplit : (k : ℂ) * ∑ j ∈ range c, ((t₀ + k * j : ℝ) : ℂ) ^ r =
      (F (t₀ + k * c) - F (t₀ + k * (0 : ℕ))) -
        ∑ j ∈ range c, (F (t₀ + k * (j + 1 : ℕ)) - F (t₀ + k * j) -
          (k : ℂ) * ((t₀ + k * j : ℝ) : ℂ) ^ r) := by
    rw [← htel, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hnorm : k * ‖∑ j ∈ range c, ((t₀ + k * j : ℝ) : ℂ) ^ r‖ ≤
      (t₀ + k * c) / |u| + t₀ / |u| + ∑ j ∈ range c, |u| * k / (t₀ + k * j) * k := by
    have e : k * ‖∑ j ∈ range c, ((t₀ + k * j : ℝ) : ℂ) ^ r‖ =
        ‖(k : ℂ) * ∑ j ∈ range c, ((t₀ + k * j : ℝ) : ℂ) ^ r‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
    rw [e, hsplit]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_))
      ((norm_sum_le _ _).trans (Finset.sum_le_sum hstep)))
    · exact norm_F_le u _ (by positivity) hu
    · simp only [CharP.cast_eq_zero, mul_zero, add_zero]
      exact norm_F_le u _ ht₀ hu
  have hu' : 0 < |u| := abs_pos.2 hu
  rw [← le_div_iff₀' hk] at hnorm
  refine hnorm.trans (le_of_eq ?_)
  rw [add_div, add_div, Finset.sum_div, div_div, div_div, add_div]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    have : 0 < t₀ + k * j := by positivity
    field_simp

/-- A finset of naturals in one residue class mod `q`, closed under betweenness within the
class, is an arithmetic progression. -/
lemma ap_structure (T : Finset ℕ) (hT : T.Nonempty) (q : ℕ) (_hq : 0 < q)
    (hmod : ∀ n ∈ T, ∀ n' ∈ T, n ≡ n' [MOD q])
    (hconv : ∀ n ∈ T, ∀ n' ∈ T, ∀ m : ℕ, n ≤ m → m ≤ n' → m ≡ n [MOD q] → m ∈ T) :
    T = (range ((T.max' hT - T.min' hT) / q + 1)).image (fun j => T.min' hT + q * j) := by
  set n₀ := T.min' hT
  set n₁ := T.max' hT
  have h0 : n₀ ∈ T := T.min'_mem hT
  have h1 : n₁ ∈ T := T.max'_mem hT
  ext n
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · intro hn
    have hle : n₀ ≤ n := T.min'_le n hn
    have hle1 : n ≤ n₁ := T.le_max' n hn
    have hdvd : q ∣ n - n₀ := (Nat.modEq_iff_dvd' hle).1 (hmod n₀ h0 n hn)
    refine ⟨(n - n₀) / q, ?_, ?_⟩
    · have : (n - n₀) / q ≤ (n₁ - n₀) / q := Nat.div_le_div_right (by omega)
      omega
    · rw [Nat.mul_div_cancel' hdvd]; omega
  · rintro ⟨j, hj, rfl⟩
    have hj' : j ≤ (n₁ - n₀) / q := by omega
    have hqj : q * j ≤ n₁ - n₀ := by
      calc q * j ≤ q * ((n₁ - n₀) / q) := Nat.mul_le_mul_left q hj'
        _ ≤ n₁ - n₀ := Nat.mul_div_le (n₁ - n₀) q
    have hn₀₁ : n₀ ≤ n₁ := T.min'_le n₁ h1
    refine hconv n₀ h0 n₁ h1 (n₀ + q * j) (by omega) (by omega) ?_
    simp [Nat.ModEq, Nat.add_mul_mod_self_left]

open Classical in
/-- The exponential sum over a progression in an interval, by telescoping (the
"comparison with the integral of `y^{iu}`"). -/
lemma prog_sum_bound (u : ℝ) (hu : u ≠ 0) (q : ℕ) (hq : 0 < q) (N : ℝ) (hqN : (q : ℝ) ≤ N)
    (J : Set ℝ) (hJ : J.OrdConnected) (hJN : J ⊆ Set.Icc N (2 * N)) (a : ℕ) :
    ‖∑ n ∈ (range (⌊2 * N⌋₊ + 1)).filter (fun n => n ≡ a [MOD q]),
        (if (n : ℝ) ∈ J then (n : ℂ) ^ (Complex.I * u) else 0)‖ ≤
      5 * N / (q * |u|) + 2 * |u| := by
  classical
  have hu' : 0 < |u| := abs_pos.2 hu
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hN : 0 < N := lt_of_lt_of_le hq' hqN
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_filter]
  set T := (range (⌊2 * N⌋₊ + 1)).filter (fun n => n ≡ a [MOD q] ∧ (n : ℝ) ∈ J)
  have hRHS : 0 ≤ 5 * N / (q * |u|) + 2 * |u| := by positivity
  rcases T.eq_empty_or_nonempty with hT | hT
  · rw [hT, Finset.sum_empty, norm_zero]; exact hRHS
  have hmemT : ∀ n ∈ T, n ≡ a [MOD q] ∧ (n : ℝ) ∈ J := fun n hn => (Finset.mem_filter.1 hn).2
  have hstr := ap_structure T hT q hq
    (fun n hn n' hn' => ((hmemT n hn).1).trans (hmemT n' hn').1.symm)
    (fun n hn n' hn' m h1 h2 h3 => by
      simp only [T, Finset.mem_filter, Finset.mem_range] at hn hn' ⊢
      refine ⟨by omega, h3.trans hn.2.1, hJ.out hn.2.2 hn'.2.2 ⟨?_, ?_⟩⟩
      · exact_mod_cast h1
      · exact_mod_cast h2)
  set n₀ := T.min' hT
  set n₁ := T.max' hT
  set c := (n₁ - n₀) / q + 1
  have hn₀J := (hmemT n₀ (T.min'_mem hT)).2
  have hn₁J := (hmemT n₁ (T.max'_mem hT)).2
  have hn₀N : N ≤ (n₀ : ℝ) := (hJN hn₀J).1
  have hn₁N : (n₁ : ℝ) ≤ 2 * N := (hJN hn₁J).2
  have hn₀₁ : n₀ ≤ n₁ := T.min'_le n₁ (T.max'_mem hT)
  rw [hstr, Finset.sum_image (fun j _ j' _ h => by
    have := Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel h); exact this)]
  have hcast : ∀ j ∈ range c, (((n₀ + q * j : ℕ) : ℂ)) ^ (Complex.I * u) =
      (((n₀ + q * j : ℝ)) : ℂ) ^ (Complex.I * u) := by
    intro j _; push_cast; rfl
  rw [Finset.sum_congr rfl hcast]
  refine (ap_sum_telescope u hu n₀ q (by linarith) hq' c).trans ?_
  -- bounds on the progression
  have hqc : (q : ℝ) * c ≤ N + q := by
    have h1 : q * ((n₁ - n₀) / q) ≤ n₁ - n₀ := Nat.mul_div_le (n₁ - n₀) q
    have h2 : ((n₁ - n₀ : ℕ) : ℝ) ≤ N := by
      rw [Nat.cast_sub hn₀₁]; linarith
    have h3 : ((q * ((n₁ - n₀) / q) : ℕ) : ℝ) ≤ ((n₁ - n₀ : ℕ) : ℝ) := by exact_mod_cast h1
    simp only [c]; push_cast at h3 ⊢; nlinarith
  have hfirst : ((n₀ : ℝ) + q * c + n₀) / (q * |u|) ≤ 5 * N / (q * |u|) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : (q : ℝ) * c ≤ n₁ - n₀ + q := by
      have h1 : q * ((n₁ - n₀) / q) ≤ n₁ - n₀ := Nat.mul_div_le (n₁ - n₀) q
      have h3 : ((q * ((n₁ - n₀) / q) : ℕ) : ℝ) ≤ ((n₁ - n₀ : ℕ) : ℝ) := by exact_mod_cast h1
      rw [Nat.cast_sub hn₀₁] at h3
      simp only [c]; push_cast at h3 ⊢; nlinarith
    have : (n₀ : ℝ) ≤ n₁ := by exact_mod_cast hn₀₁
    nlinarith
  have hsecond : ∑ j ∈ range c, (q : ℝ) * |u| / (n₀ + q * j) ≤ 2 * |u| := by
    calc ∑ j ∈ range c, (q : ℝ) * |u| / (n₀ + q * j) ≤ ∑ j ∈ range c, (q : ℝ) * |u| / N := by
          refine Finset.sum_le_sum fun j _ => ?_
          apply div_le_div_of_nonneg_left (by positivity) hN
          have : (0 : ℝ) ≤ q * j := by positivity
          linarith
      _ = (q * c) * |u| / N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ (N + N) * |u| / N := by
          apply div_le_div_of_nonneg_right _ hN.le
          exact mul_le_mul_of_nonneg_right (by linarith) hu'.le
      _ = 2 * |u| := by field_simp; ring
  linarith

/-! ## Brun's pure sieve and character sums -/

lemma prod_dvd_iff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (m : ℕ) :
    (∀ p ∈ S, p ∣ m) ↔ (∏ p ∈ S, p) ∣ m :=
  ⟨fun h => Finset.prod_primes_dvd m (fun p hp => (hS p hp).prime) h,
    fun h _ hp => (Finset.dvd_prod_of_mem _ hp).trans h⟩

open Classical in
/-- Brun's pure sieve (Bonferroni truncation) for a weighted sum over integers free of the
primes in `P`. -/
lemma sieve_decomp (R P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) (c : ℕ → ℂ) :
    ‖∑ m ∈ R, (if ∀ p ∈ P, ¬ p ∣ m then c m else 0) -
        ∑ S ∈ P.powerset, (if S.card < n then (-1 : ℂ) ^ S.card *
          ∑ m ∈ R, (if (∏ p ∈ S, p) ∣ m then c m else 0) else 0)‖ ≤
      ∑ S ∈ P.powerset, (if S.card = n then
          ∑ m ∈ R, (if (∏ p ∈ S, p) ∣ m then ‖c m‖ else 0) else 0) := by
  let a : ℕ → ℕ → ℝ := fun m p => if p ∣ m then 1 else 0
  have ha : ∀ m, ∀ p ∈ P, 0 ≤ a m p ∧ a m p ≤ 1 := fun m p _ => by
    simp only [a]; split_ifs <;> norm_num
  have hind : ∀ m, (if ∀ p ∈ P, ¬ p ∣ m then (1 : ℝ) else 0) = ∏ p ∈ P, (1 - a m p) := by
    intro m
    simp only [a]
    rw [show (fun p => (1 : ℝ) - if p ∣ m then 1 else 0) = fun p => if ¬ p ∣ m then 1 else 0 from
      funext fun p => by split_ifs <;> norm_num, Finset.prod_boole]
  have hprod : ∀ m, ∀ S ∈ P.powerset, ∏ p ∈ S, a m p = if (∏ p ∈ S, p) ∣ m then 1 else 0 := by
    intro m S hS
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hP p (Finset.mem_powerset.1 hS hp)
    simp only [a]
    rw [Finset.prod_boole]
    simp only [prod_dvd_iff S hS' m]
  -- rewrite both sums pointwise in `m`
  have e1 : ∑ m ∈ R, (if ∀ p ∈ P, ¬ p ∣ m then c m else 0) =
      ∑ m ∈ R, c m * ((∏ p ∈ P, (1 - a m p) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← hind m]; split_ifs <;> simp
  have e2 : ∑ S ∈ P.powerset, (if S.card < n then (-1 : ℂ) ^ S.card *
        ∑ m ∈ R, (if (∏ p ∈ S, p) ∣ m then c m else 0) else 0) =
      ∑ m ∈ R, c m * ((bonfTrunc P (a m) n : ℝ) : ℂ) := by
    simp only [bonfTrunc]
    push_cast
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S hS => ?_
    split_ifs with h
    · refine Finset.sum_congr rfl fun m _ => ?_
      have := hprod m S hS
      rw [this]
      split_ifs <;> push_cast <;> ring
    · simp
  have e3 : ∑ S ∈ P.powerset, (if S.card = n then
          ∑ m ∈ R, (if (∏ p ∈ S, p) ∣ m then ‖c m‖ else 0) else 0) =
      ∑ m ∈ R, ‖c m‖ * esym P (a m) n := by
    simp only [esym, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S hS => ?_
    split_ifs with h
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [hprod m S hS]
      split_ifs <;> simp
    · simp
  rw [e1, e2, e3, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (bonferroni (a m) P (ha m) n) (norm_nonneg _)

open Classical in
/-- Reindexing multiples of `d`. -/
lemma sum_dvd_reindex (B d : ℕ) (hd : 0 < d) (g : ℕ → ℂ) :
    ∑ m ∈ range B, (if d ∣ m then g m else 0) =
      ∑ t ∈ range B, (if d * t < B then g (d * t) else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have : (range B).filter (fun m => d ∣ m) =
      ((range B).filter (fun t => d * t < B)).image (fun t => d * t) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hm, t, rfl⟩
      refine ⟨t, ⟨?_, hm⟩, rfl⟩
      exact lt_of_le_of_lt (Nat.le_mul_of_pos_left t hd) hm
    · rintro ⟨t, ⟨_, ht⟩, rfl⟩
      exact ⟨ht, dvd_mul_right d t⟩
  rw [this, Finset.sum_image (fun t _ t' _ h => Nat.eq_of_mul_eq_mul_left hd h)]

/-- Splitting a sum into residue classes. -/
lemma sum_residues (s : Finset ℕ) (k : ℕ) (hk : 0 < k) (f : ℕ → ℂ) :
    ∑ t ∈ s, f t = ∑ b ∈ range k, ∑ t ∈ s.filter (fun t => t ≡ b [MOD k]), f t := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun t => t % k) (t := range k)
    (fun t _ => Finset.mem_range.2 (Nat.mod_lt t hk))]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' : b % k = b := Nat.mod_eq_of_lt (Finset.mem_range.1 hb)
  congr 1
  ext t
  simp only [Finset.mem_filter, Nat.ModEq, hb']

lemma card_powerset_le (P : Finset ℕ) :
    ∀ n : ℕ, (∑ S ∈ P.powerset, (if S.card ≤ n then (1 : ℝ) else 0)) ≤ ((P.card : ℝ) + 1) ^ n := by
  induction P using Finset.induction_on with
  | empty =>
    intro n
    rw [Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, if_pos (Nat.zero_le n)]
    simp
  | insert q P hq ih =>
    intro n
    rw [Finset.sum_powerset_insert hq, Finset.card_insert_of_notMem hq]
    cases n with
    | zero =>
      have h1 : ∑ S ∈ P.powerset, (if S.card ≤ 0 then (1 : ℝ) else 0) ≤ 1 := by
        have := ih 0; rwa [pow_zero] at this
      have h2 : ∑ S ∈ P.powerset, (if (insert q S).card ≤ 0 then (1 : ℝ) else 0) = 0 := by
        refine Finset.sum_eq_zero fun S hS => ?_
        rw [if_neg]; have := Finset.card_pos.2 (Finset.insert_nonempty q S); omega
      rw [h2]; simp only [add_zero, pow_zero]; exact h1
    | succ n =>
      have h2 : ∑ S ∈ P.powerset, (if (insert q S).card ≤ n + 1 then (1 : ℝ) else 0) =
          ∑ S ∈ P.powerset, (if S.card ≤ n then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun S hS => ?_
        have hqS : q ∉ S := fun h => hq (Finset.mem_powerset.1 hS h)
        rw [Finset.card_insert_of_notMem hqS]
        simp only [add_le_add_iff_right]
      rw [h2]
      have hb := pow_succ_add_le ((P.card : ℝ) + 1) 1 (by positivity) zero_le_one n
      have hp : (1 : ℝ) ≤ ((P.card : ℝ) + 1) ^ n := one_le_pow₀ (by linarith [(Nat.cast_nonneg P.card : (0:ℝ) ≤ P.card)])
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have := ih (n + 1)
      have := ih n
      push_cast
      have : ((P.card : ℝ) + 1) ^ n ≤ (n + 1) * 1 * ((P.card : ℝ) + 1) ^ n := by nlinarith
      nlinarith

/-! ## Dilated intervals -/

/-- The set `{y : d y ∈ J}`. -/
def scaleSet (d : ℕ) (J : Set ℝ) : Set ℝ := (fun y : ℝ => (d : ℝ) * y) ⁻¹' J

lemma scaleSet_ordConnected (d : ℕ) (J : Set ℝ) (hJ : J.OrdConnected) :
    (scaleSet d J).OrdConnected := by
  refine ⟨fun y₁ h₁ y₂ h₂ y hy => ?_⟩
  simp only [scaleSet, Set.mem_preimage] at h₁ h₂ ⊢
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  exact hJ.out h₁ h₂ ⟨mul_le_mul_of_nonneg_left hy.1 hd, mul_le_mul_of_nonneg_left hy.2 hd⟩

lemma scaleSet_subset (d : ℕ) (hd : 0 < d) (J : Set ℝ) (M : ℝ) (hJ : J ⊆ Set.Icc M (2 * M)) :
    scaleSet d J ⊆ Set.Icc (M / d) (2 * (M / d)) := by
  intro y hy
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have := hJ hy
  simp only [Set.mem_Icc] at this ⊢
  constructor
  · rw [div_le_iff₀ hd']; linarith
  · rw [← mul_div_assoc, le_div_iff₀ hd']; linarith

end ArtinPrimitiveRoots.A106S
end

section
/-!
# Divisor masses for the Bonferroni truncation of the `W`-rough indicator

`P` is the set of primes `≤ W` and `d_S = ∏_{p ∈ S} p` for `S ⊆ P`. The reciprocal sums of
the truncated divisors are controlled by `V(W)`:
`Σ_{S ⊆ P} c^{|S|} / d_S = ∏_{p ≤ W} (1 + c/p) ≤ exp(-c log V(W))`, which gives (5.6) of [21]
(`c = 1`) and, by Rankin's trick (`c = 2`), the first omitted degree
`Σ_{|S| = n} 1/d_S ≤ 2^{-n} exp(-2 log V(W))`.
-/

namespace ArtinPrimitiveRoots.A106T

open Real Set Filter

/-- The primes `≤ W`. -/
noncomputable def Pset (W : ℝ) : Finset ℕ := (Finset.range (⌊W⌋₊ + 1)).filter Nat.Prime

lemma mem_Pset {W : ℝ} {p : ℕ} : p ∈ Pset W ↔ p.Prime ∧ p ≤ ⌊W⌋₊ := by
  simp [Pset, and_comm]

lemma Pset_prime {W : ℝ} : ∀ p ∈ Pset W, p.Prime := fun _ hp => (mem_Pset.1 hp).1

lemma mertensProduct_eq (W : ℝ) : mertensProduct W = ∏ p ∈ Pset W, (1 - 1 / (p : ℝ)) := rfl

lemma isRough_iff {W : ℝ} (hW : 0 ≤ W) {m : ℕ} (hm : 0 < m) :
    IsRough W m ↔ ∀ p ∈ Pset W, ¬ p ∣ m := by
  constructor
  · rintro ⟨-, h⟩ p hp hpm
    rw [mem_Pset] at hp
    have := h p (Nat.mem_primeFactors.2 ⟨hp.1, hpm, hm.ne'⟩)
    have h2 : (p : ℝ) ≤ W := (Nat.le_floor_iff hW).1 hp.2
    linarith
  · intro h
    refine ⟨hm, fun p hp => ?_⟩
    rw [Nat.mem_primeFactors] at hp
    by_contra hcon
    push Not at hcon
    exact h p (mem_Pset.2 ⟨hp.1, Nat.le_floor hcon⟩) hp.2.1

open Classical in
/-- Counting multiples of `d` in `[M, 2M]`. -/
lemma card_multiples_le {M : ℝ} (hM : 0 < M) {d : ℕ} (hd : 0 < d) (B : ℕ) (J : Set ℝ)
    (hJ : J ⊆ Icc M (2 * M)) :
    (((Finset.range B).filter (fun m : ℕ => (m : ℝ) ∈ J ∧ d ∣ m)).card : ℝ) ≤ M / d + 1 := by
  classical
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set Z := (Finset.range B).filter (fun m : ℕ => (m : ℝ) ∈ J ∧ d ∣ m)
  have hinj : Set.InjOn (fun m : ℕ => m / d) (Z : Set ℕ) := by
    intro m₁ h₁ m₂ h₂ h
    simp only [Z, Finset.coe_filter, Set.mem_ofPred_eq] at h₁ h₂
    have e1 := Nat.div_mul_cancel h₁.2.2
    have e2 := Nat.div_mul_cancel h₂.2.2
    simp only at h
    rw [← e1, ← e2, h]
  have hmaps : ∀ m ∈ Z, m / d ∈ Finset.Icc ⌈M / d⌉₊ ⌊2 * M / d⌋₊ := by
    intro m hm
    simp only [Z, Finset.mem_filter] at hm
    obtain ⟨-, hmJ, hdm⟩ := hm
    obtain ⟨h1, h2⟩ := hJ hmJ
    have e : ((m / d : ℕ) : ℝ) = (m : ℝ) / d := Nat.cast_div hdm hdpos.ne'
    rw [Finset.mem_Icc]
    constructor
    · rw [Nat.ceil_le, e]; exact div_le_div_of_nonneg_right h1 hdpos.le
    · rw [Nat.le_floor_iff (by positivity), e]; exact div_le_div_of_nonneg_right h2 hdpos.le
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Nat.card_Icc] at hcard
  calc (Z.card : ℝ) ≤ ((⌊2 * M / d⌋₊ + 1 - ⌈M / d⌉₊ : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ M / d + 1 := by
      rcases le_or_gt ⌈M / d⌉₊ (⌊2 * M / d⌋₊ + 1) with h | h
      · rw [Nat.cast_sub h]
        push_cast
        have h1 := Nat.floor_le (show 0 ≤ 2 * M / d by positivity)
        have h2 := Nat.le_ceil (M / d)
        have : 2 * M / d = 2 * (M / d) := by ring
        linarith
      · rw [Nat.sub_eq_zero_of_le h.le]; push_cast; positivity

/-- The products `∏ (1 + c/p)` over primes `≤ W` are at most `exp(-c log V(W))`. -/
lemma prod_one_add_le {W c : ℝ} (hc : 0 ≤ c) :
    ∏ p ∈ Pset W, (1 + c / (p : ℝ)) ≤ exp (-(c * log (mertensProduct W))) := by
  have h2le : ∀ p ∈ Pset W, (2 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (mem_Pset.1 hp).1.two_le
  have hfac : ∀ p ∈ Pset W, 0 < 1 - 1 / (p : ℝ) := by
    intro p hp
    have := h2le p hp
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hlog : log (mertensProduct W) = ∑ p ∈ Pset W, log (1 - 1 / (p : ℝ)) := by
    rw [mertensProduct_eq, Real.log_prod]
    intro p hp; exact (hfac p hp).ne'
  have hsum : ∑ p ∈ Pset W, c / (p : ℝ) ≤ -(c * log (mertensProduct W)) := by
    rw [hlog, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun p hp => ?_
    have h1 := Real.log_le_sub_one_of_pos (hfac p hp)
    have : c / (p : ℝ) = c * (1 / p) := by ring
    rw [this]
    nlinarith
  calc ∏ p ∈ Pset W, (1 + c / (p : ℝ)) ≤ ∏ p ∈ Pset W, exp (c / (p : ℝ)) := by
        refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => ?_)
        · have := h2le p hp; positivity
        · have := Real.add_one_le_exp (c / (p : ℝ)); linarith
    _ = exp (∑ p ∈ Pset W, c / (p : ℝ)) := (Real.exp_sum _ _).symm
    _ ≤ exp (-(c * log (mertensProduct W))) := Real.exp_le_exp.2 hsum

lemma prod_inv_cast (D : Finset ℕ) : (1 / ((∏ p ∈ D, p : ℕ) : ℝ)) = ∏ p ∈ D, (1 / (p : ℝ)) := by
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const_one]

/-- `Σ_{S ⊆ P} c^{|S|} / d_S = ∏ (1 + c/p)`. -/
lemma sum_powerset_eq_prod (W c : ℝ) :
    ∑ D ∈ (Pset W).powerset, c ^ D.card * (1 / ((∏ p ∈ D, p : ℕ) : ℝ)) =
      ∏ p ∈ Pset W, (1 + c / (p : ℝ)) := by
  have := Finset.prod_add (fun p : ℕ => c / (p : ℝ)) (fun _ => (1 : ℝ)) (Pset W)
  simp only [Finset.prod_const_one, mul_one] at this
  rw [show ∏ p ∈ Pset W, (1 + c / (p : ℝ)) = ∏ p ∈ Pset W, (c / (p : ℝ) + 1) from
    Finset.prod_congr rfl (fun _ _ => add_comm _ _), this]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [prod_inv_cast, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  ring

/-- (5.6): the reciprocal mass of the truncated divisors is at most `1/V(W)`. -/
lemma sum_trunc_inv_le (W : ℝ) (n : ℕ) :
    ∑ S ∈ (Pset W).powerset, (if S.card < n then 1 / ((∏ p ∈ S, p : ℕ) : ℝ) else 0) ≤
      exp (-(1 * log (mertensProduct W))) := by
  refine le_trans ?_ ((sum_powerset_eq_prod W 1).le.trans (prod_one_add_le zero_le_one))
  refine Finset.sum_le_sum fun S _ => ?_
  rw [one_pow, one_mul]
  split_ifs
  · exact le_rfl
  · positivity

/-- Rankin: the first omitted degree has reciprocal mass at most `2^{-n} exp(-2 log V(W))`. -/
lemma sum_card_inv_le (W : ℝ) (n : ℕ) :
    ∑ S ∈ (Pset W).powerset, (if S.card = n then 1 / ((∏ p ∈ S, p : ℕ) : ℝ) else 0) ≤
      (1 / 2) ^ n * exp (-(2 * log (mertensProduct W))) := by
  have h := (sum_powerset_eq_prod W 2).le.trans (prod_one_add_le (W := W) zero_le_two)
  have hle : 2 ^ n * ∑ S ∈ (Pset W).powerset,
      (if S.card = n then 1 / ((∏ p ∈ S, p : ℕ) : ℝ) else 0) ≤
      ∑ D ∈ (Pset W).powerset, (2 : ℝ) ^ D.card * (1 / ((∏ p ∈ D, p : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun S _ => ?_
    split_ifs with hS
    · rw [hS]
    · rw [mul_zero]; positivity
  have := hle.trans h
  rw [one_div_pow, one_div_mul_eq_div, le_div_iff₀ (by positivity), mul_comm]
  exact this

lemma card_Pset_le {W : ℝ} (hW : 0 ≤ W) : ((Pset W).card : ℝ) ≤ W + 1 := by
  have := Finset.card_filter_le (Finset.range (⌊W⌋₊ + 1)) Nat.Prime
  rw [Finset.card_range] at this
  have h2 : ((⌊W⌋₊ + 1 : ℕ) : ℝ) ≤ W + 1 := by push_cast; linarith [Nat.floor_le hW]
  exact (by exact_mod_cast this : ((Pset W).card : ℝ) ≤ ((⌊W⌋₊ + 1 : ℕ) : ℝ)).trans h2

lemma prod_le_pow {W : ℝ} (hW : 1 ≤ W) {D : Finset ℕ} (hD : D ⊆ Pset W) :
    ((∏ p ∈ D, p : ℕ) : ℝ) ≤ W ^ D.card := by
  push_cast
  rw [← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun p hp => ?_
  exact (Nat.le_floor_iff (by linarith)).1 (mem_Pset.1 (hD hp)).2

lemma prod_pos (D : Finset ℕ) {W : ℝ} (hD : D ⊆ Pset W) : 0 < ∏ p ∈ D, p :=
  Finset.prod_pos fun _ hp => (mem_Pset.1 (hD hp)).1.pos

end ArtinPrimitiveRoots.A106T
end

section
/-!
# The growth conditions for (10.19)

With `L = log x`, `W = exp(L^{0.24})`, `n = ⌈L^{0.1}⌉`, `T* = exp(L/(log L)²)`, for large `x`:
`2^{-n} ≤ L^{-(A₄+2)}`, `L^{A₀} T* (W+2)^n ≤ x^{w/2}` and `L^{A₄} ≤ x^{w/2}`.
-/

namespace ArtinPrimitiveRoots.A106T

open Real Filter

lemma ev_L (A₀ A₄ w : ℝ) (hA₀ : 0 < A₀) (hA₄ : 0 < A₄) (hw : 0 < w) :
    ∀ᶠ L in atTop, 2 ≤ L ∧ (A₄ + 2) * log L ≤ L ^ (0.1 : ℝ) * log 2 ∧
      A₀ * log L + L / log L ^ 2 + 6 * L ^ (0.34 : ℝ) ≤ w / 2 * L ∧
      A₄ * log L ≤ w / 2 * L := by
  have hl2 : 0 < log (2 : ℝ) := log_pos one_lt_two
  have h1 := (isLittleO_log_rpow_atTop (r := (0.1 : ℝ)) (by norm_num)).bound
    (div_pos hl2 (by linarith : (0 : ℝ) < A₄ + 2))
  have h2 := (isLittleO_log_rpow_atTop (r := (1 : ℝ)) one_pos).bound
    (div_pos (by positivity : 0 < w / 6) hA₀)
  have h3 := (isLittleO_log_rpow_atTop (r := (1 : ℝ)) one_pos).bound
    (div_pos (by positivity : 0 < w / 2) hA₄)
  have h4 := tendsto_log_atTop.eventually_ge_atTop (6 / w + 1)
  have h5 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.66)).eventually_ge_atTop (36 / w)
  filter_upwards [h1, h2, h3, h4, h5, eventually_ge_atTop (2 : ℝ)] with L h1 h2 h3 h4 h5 h6
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < log L := log_pos (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogL, abs_of_pos (by positivity)] at h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogL, rpow_one, abs_of_pos hL0] at h2 h3
  refine ⟨h6, ?_, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)] at h1
    linarith
  · have e2 : A₀ * log L ≤ w / 6 * L := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hA₀] at h2; linarith
    have e3 : L / log L ^ 2 ≤ w / 6 * L := by
      have hsq : 6 / w ≤ log L ^ 2 := by
        have : 6 / w ≤ log L := by linarith
        nlinarith
      rw [div_le_iff₀ (by positivity)]
      calc L = w / 6 * L * (6 / w) := by field_simp
        _ ≤ w / 6 * L * log L ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    have e4 : 6 * L ^ (0.34 : ℝ) ≤ w / 6 * L := by
      have hsplit : L = L ^ (0.34 : ℝ) * L ^ (0.66 : ℝ) := by
        rw [← rpow_add hL0]; norm_num
      have hpos : 0 < L ^ (0.34 : ℝ) := rpow_pos_of_pos hL0 _
      calc 6 * L ^ (0.34 : ℝ) = w / 6 * (L ^ (0.34 : ℝ) * (36 / w)) := by field_simp; ring
        _ ≤ w / 6 * (L ^ (0.34 : ℝ) * L ^ (0.66 : ℝ)) := by gcongr
        _ = w / 6 * L := by rw [← hsplit]
    linarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ hA₄] at h3; linarith

lemma ev_x (A₀ A₄ w : ℝ) (hA₀ : 0 < A₀) (hA₄ : 0 < A₄) (hw : 0 < w) :
    ∀ᶠ x in atTop, 2 ≤ log x ∧
      (1 / 2 : ℝ) ^ ⌈log x ^ (0.1 : ℝ)⌉₊ ≤ log x ^ (-(A₄ + 2)) ∧
      log x ^ A₀ * exp (log x / log (log x) ^ 2) *
          (sieveLevel x + 2) ^ ⌈log x ^ (0.1 : ℝ)⌉₊ ≤ x ^ (w / 2) ∧
      log x ^ A₄ ≤ x ^ (w / 2) := by
  filter_upwards [tendsto_log_atTop.eventually (ev_L A₀ A₄ w hA₀ hA₄ hw),
    eventually_gt_atTop (0 : ℝ)] with x hx hx0
  obtain ⟨h2, h1, h3, h4⟩ := hx
  set L := log x with hL
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < log L := log_pos (by linarith)
  set n := ⌈L ^ (0.1 : ℝ)⌉₊ with hn
  have hn1 : L ^ (0.1 : ℝ) ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) < L ^ (0.1 : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hxw : x ^ (w / 2) = exp (w / 2 * L) := by
    rw [rpow_def_of_pos hx0, hL, mul_comm]
  refine ⟨h2, ?_, ?_, ?_⟩
  · -- (1/2)^n ≤ L^{-(A₄+2)}
    have e1 : (1 / 2 : ℝ) ^ n = exp (-(n * log 2)) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2), ← Real.exp_nat_mul, one_div,
        Real.log_inv]
      ring_nf
    rw [e1, rpow_def_of_pos hL0]
    refine Real.exp_le_exp.2 ?_
    have : L ^ (0.1 : ℝ) * log 2 ≤ n * log 2 :=
      mul_le_mul_of_nonneg_right hn1 (log_nonneg one_le_two)
    linarith
  · -- L^{A₀} T* (W+2)^n ≤ x^{w/2}
    have hW1 : 1 ≤ sieveLevel x := by
      unfold sieveLevel; exact Real.one_le_exp (by positivity)
    have hW2 : sieveLevel x + 2 ≤ exp (L ^ (0.24 : ℝ) + 2) := by
      rw [Real.exp_add]
      have : (3 : ℝ) ≤ exp 2 := by
        have := Real.add_one_le_exp (2 : ℝ); linarith
      have hW : sieveLevel x = exp (L ^ (0.24 : ℝ)) := rfl
      rw [← hW]
      nlinarith
    have hpow : (sieveLevel x + 2) ^ n ≤ exp (n * (L ^ (0.24 : ℝ) + 2)) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by linarith) hW2 n
    have hab : (n : ℝ) * (L ^ (0.24 : ℝ) + 2) ≤ 6 * L ^ (0.34 : ℝ) := by
      have ha : 1 ≤ L ^ (0.1 : ℝ) := one_le_rpow (by linarith) (by norm_num)
      have hb : 1 ≤ L ^ (0.24 : ℝ) := one_le_rpow (by linarith) (by norm_num)
      have hab : L ^ (0.34 : ℝ) = L ^ (0.1 : ℝ) * L ^ (0.24 : ℝ) := by
        rw [← rpow_add hL0]; norm_num
      rw [hab]
      have : (n : ℝ) * (L ^ (0.24 : ℝ) + 2) ≤ (L ^ (0.1 : ℝ) + 1) * (L ^ (0.24 : ℝ) + 2) :=
        mul_le_mul_of_nonneg_right hn2.le (by positivity)
      nlinarith
    have hA : L ^ A₀ = exp (A₀ * log L) := by rw [rpow_def_of_pos hL0, mul_comm]
    calc L ^ A₀ * exp (L / log L ^ 2) * (sieveLevel x + 2) ^ n
        ≤ exp (A₀ * log L) * exp (L / log L ^ 2) * exp (n * (L ^ (0.24 : ℝ) + 2)) := by
          rw [hA]; gcongr
      _ = exp (A₀ * log L + L / log L ^ 2 + n * (L ^ (0.24 : ℝ) + 2)) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ exp (w / 2 * L) := Real.exp_le_exp.2 (by linarith)
      _ = x ^ (w / 2) := hxw.symm
  · rw [hxw, rpow_def_of_pos hL0, mul_comm]
    exact Real.exp_le_exp.2 h4

end ArtinPrimitiveRoots.A106T
end

section
/-!
# (10.19): the `W`-rough sum twisted by `χ(m) m^{iu} / log m`

Following [21, Lemma 5.2]: truncate `1_{P⁻(m) > W}` by Bonferroni at depth `n` (`sieve_decomp`);
the first omitted degree costs `M 2^{-n} V(W)^{-2} + (|P|+1)^n` (Rankin). For each truncated
divisor `d`, write `m = d t` and split `t` into residues modulo `k`; on each progression use
the sum–integral comparison `prog_sum_bound` when `|u| ≤ T*` and `log_phase_progression` when
`|u| > T*`. The reciprocal mass of the divisors is at most `1/V(W)`. Finally `1/log m` is
removed by the layer-cake partial summation. `mertens_product` gives `V(W) ≫ 1/L`, needed
because of the normalisation `1/(M V(W))`.
-/

namespace ArtinPrimitiveRoots.A106T

open Real Set Filter Topology

/-! ## One divisor -/

open Classical in
/-- The multiples of `d` in an interval: `m = d t`, split `t` into residues modulo `k`. -/
lemma dvd_sum_bound {M : ℝ} (hM : 0 < M) {k : ℕ} (hk : 0 < k) (χ : DirichletCharacter ℂ k)
    (u : ℝ) (J' : Set ℝ) (hJ'sub : J' ⊆ Icc M (2 * M)) {d : ℕ} (hd : 0 < d) (Bnd : ℝ)
    (hB : ∀ b : ℕ, ‖∑ t ∈ (Finset.range (⌊2 * (M / d)⌋₊ + 1)).filter (fun t => t ≡ b [MOD k]),
      (if (t : ℝ) ∈ A106S.scaleSet d J' then (t : ℂ) ^ (Complex.I * u) else 0)‖ ≤ Bnd) :
    ‖∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1), (if d ∣ m then
      (if (m : ℝ) ∈ J' then χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * u) else 0) else 0)‖ ≤
      k * Bnd := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set B := ⌊2 * M⌋₊ + 1 with hBdef
  set B' := ⌊2 * (M / d)⌋₊ + 1 with hB'def
  set sc := A106S.scaleSet d J' with hsc
  have hmem : ∀ t : ℕ, (((d * t : ℕ) : ℝ) ∈ J') ↔ ((t : ℝ) ∈ sc) := by
    intro t; simp [hsc, A106S.scaleSet]
  have hscsub : sc ⊆ Icc (M / d) (2 * (M / d)) := A106S.scaleSet_subset d hd J' M hJ'sub
  rw [A106S.sum_dvd_reindex B d hd]
  -- move to the smaller range
  have hsub : Finset.range B' ⊆ Finset.range B := by
    refine Finset.range_subset_range.2 (Nat.succ_le_succ (Nat.floor_le_floor ?_))
    rw [mul_div_assoc']
    exact div_le_self (by positivity) (by exact_mod_cast hd)
  have hstep1 : (∑ t ∈ Finset.range B, (if d * t < B then
      (if ((d * t : ℕ) : ℝ) ∈ J' then χ ((d * t : ℕ) : ZMod k) * ((d * t : ℕ) : ℂ) ^ (Complex.I * u)
        else 0) else 0)) =
      ∑ t ∈ Finset.range B', (if (t : ℝ) ∈ sc then
        χ (d : ZMod k) * (d : ℂ) ^ (Complex.I * u) * (χ (t : ZMod k) * (t : ℂ) ^ (Complex.I * u))
        else 0) := by
    symm
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun t _ => ?_
      by_cases ht : (t : ℝ) ∈ sc
      · have htJ := (hmem t).2 ht
        have hlt : d * t < B := by
          have := (hJ'sub htJ).2
          have h2 := Nat.floor_le_floor this
          rw [Nat.floor_natCast] at h2
          omega
        rw [if_pos ht, if_pos hlt, if_pos htJ]
        push_cast
        rw [map_mul, Complex.natCast_mul_natCast_cpow]
        ring
      · rw [if_neg ht]
        split_ifs with h1 h2
        · exact absurd ((hmem t).1 h2) ht
        · rfl
        · rfl
    · intro t _ ht
      have hnot : (t : ℝ) ∉ sc := by
        intro hsc'
        have := (hscsub hsc').2
        have h2 := Nat.floor_le_floor this
        rw [Nat.floor_natCast] at h2
        exact ht (Finset.mem_range.2 (by omega))
      have hJ : ((d * t : ℕ) : ℝ) ∉ J' := fun h => hnot ((hmem t).1 h)
      rw [if_neg hJ, ite_self]
  set A : ℂ := χ (d : ZMod k) * (d : ℂ) ^ (Complex.I * u) with hA
  have hAn : ‖A‖ ≤ 1 := by
    rw [hA, norm_mul, Complex.norm_natCast_cpow_of_pos hd]
    simpa using DirichletCharacter.norm_le_one χ (d : ZMod k)
  have hfac : (∑ t ∈ Finset.range B', (if (t : ℝ) ∈ sc then
      A * (χ (t : ZMod k) * (t : ℂ) ^ (Complex.I * u)) else 0)) =
      A * ∑ t ∈ Finset.range B', (if (t : ℝ) ∈ sc then
        χ (t : ZMod k) * (t : ℂ) ^ (Complex.I * u) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp
  rw [hstep1, hfac, A106S.sum_residues _ k hk, norm_mul]
  have hinner : ∀ b ∈ Finset.range k,
      ‖∑ t ∈ (Finset.range B').filter (fun t => t ≡ b [MOD k]), (if (t : ℝ) ∈ sc then
        χ (t : ZMod k) * (t : ℂ) ^ (Complex.I * u) else 0)‖ ≤ Bnd := by
    intro b _
    have e : (∑ t ∈ (Finset.range B').filter (fun t => t ≡ b [MOD k]), (if (t : ℝ) ∈ sc then
        χ (t : ZMod k) * (t : ℂ) ^ (Complex.I * u) else 0)) =
        χ (b : ZMod k) * ∑ t ∈ (Finset.range B').filter (fun t => t ≡ b [MOD k]),
          (if (t : ℝ) ∈ sc then (t : ℂ) ^ (Complex.I * u) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      have htb : (t : ZMod k) = (b : ZMod k) :=
        (ZMod.natCast_eq_natCast_iff t b k).2 (Finset.mem_filter.1 ht).2
      rw [htb]
      split_ifs <;> simp
    rw [e, norm_mul]
    calc ‖χ (b : ZMod k)‖ * _ ≤ 1 * Bnd :=
          mul_le_mul (DirichletCharacter.norm_le_one χ _) (hB b) (norm_nonneg _) zero_le_one
      _ = Bnd := one_mul _
  calc ‖A‖ * ‖∑ b ∈ Finset.range k, ∑ t ∈ (Finset.range B').filter (fun t => t ≡ b [MOD k]),
        (if (t : ℝ) ∈ sc then χ (t : ZMod k) * (t : ℂ) ^ (Complex.I * u) else 0)‖
      ≤ 1 * ∑ b ∈ Finset.range k, Bnd :=
        mul_le_mul hAn ((norm_sum_le _ _).trans (Finset.sum_le_sum hinner)) (norm_nonneg _)
          zero_le_one
    _ = k * Bnd := by rw [one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## The truncated sieve on one subinterval -/

open Classical in
/-- Bonferroni at depth `n`, then `dvd_sum_bound` for each truncated divisor; the first omitted
degree is bounded by counting multiples. -/
lemma core_bound {W M : ℝ} (hW : 0 ≤ W) (hM : 0 < M) {k : ℕ} (hk : 0 < k)
    (χ : DirichletCharacter ℂ k) (u : ℝ) (n : ℕ) (J' : Set ℝ) (hJ'sub : J' ⊆ Icc M (2 * M))
    (Bnd : ℕ → ℝ)
    (hB : ∀ S ∈ (Pset W).powerset, S.card < n → ∀ b : ℕ,
      ‖∑ t ∈ (Finset.range (⌊2 * (M / ((∏ p ∈ S, p : ℕ) : ℝ))⌋₊ + 1)).filter
          (fun t => t ≡ b [MOD k]),
        (if (t : ℝ) ∈ A106S.scaleSet (∏ p ∈ S, p) J' then (t : ℂ) ^ (Complex.I * u) else 0)‖ ≤
        Bnd (∏ p ∈ S, p)) :
    ‖∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
        (if (m : ℝ) ∈ J' ∧ IsRough W m then χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * u) else 0)‖ ≤
      ∑ S ∈ (Pset W).powerset, (if S.card < n then k * Bnd (∏ p ∈ S, p) else 0) +
        ∑ S ∈ (Pset W).powerset,
          (if S.card = n then M / ((∏ p ∈ S, p : ℕ) : ℝ) + 1 else 0) := by
  set R := Finset.range (⌊2 * M⌋₊ + 1)
  set c : ℕ → ℂ := fun m =>
    if (m : ℝ) ∈ J' then χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * u) else 0 with hc
  have h1 : (∑ m ∈ R, (if (m : ℝ) ∈ J' ∧ IsRough W m then
      χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * u) else 0)) =
      ∑ m ∈ R, (if ∀ p ∈ Pset W, ¬ p ∣ m then c m else 0) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : (m : ℝ) ∈ J'
    · have hm0 : 0 < m := by
        have := (hJ'sub hm).1
        exact_mod_cast hM.trans_le this
      have hr := isRough_iff hW hm0
      by_cases h : ∀ p ∈ Pset W, ¬ p ∣ m
      · rw [if_pos ⟨hm, hr.2 h⟩, if_pos h, hc]; simp only [if_pos hm]
      · rw [if_neg (fun h' => h (hr.1 h'.2)), if_neg h]
    · rw [if_neg (fun h' => hm h'.1)]
      split_ifs <;> simp [hc, hm]
  have hdec := A106S.sieve_decomp R (Pset W) Pset_prime n c
  rw [h1]
  set X := ∑ m ∈ R, (if ∀ p ∈ Pset W, ¬ p ∣ m then c m else 0)
  set Y := ∑ S ∈ (Pset W).powerset, (if S.card < n then (-1 : ℂ) ^ S.card *
    ∑ m ∈ R, (if (∏ p ∈ S, p) ∣ m then c m else 0) else 0)
  have hY : ‖Y‖ ≤ ∑ S ∈ (Pset W).powerset, (if S.card < n then k * Bnd (∏ p ∈ S, p) else 0) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun S hS => ?_)
    split_ifs with hSn
    · rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact dvd_sum_bound hM hk χ u J' hJ'sub
        (prod_pos S (Finset.mem_powerset.1 hS)) _ (hB S hS hSn)
    · simp
  have hE : ∑ S ∈ (Pset W).powerset, (if S.card = n then
      ∑ m ∈ R, (if (∏ p ∈ S, p) ∣ m then ‖c m‖ else 0) else 0) ≤
      ∑ S ∈ (Pset W).powerset,
        (if S.card = n then M / ((∏ p ∈ S, p : ℕ) : ℝ) + 1 else 0) := by
    refine Finset.sum_le_sum fun S hS => ?_
    split_ifs with hSn
    · have hd := prod_pos S (Finset.mem_powerset.1 hS)
      refine le_trans ?_ (card_multiples_le hM hd (⌊2 * M⌋₊ + 1) J' hJ'sub)
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_le_sum fun m _ => ?_
      by_cases hm : (m : ℝ) ∈ J'
      · split_ifs with h2 h3
        · simp only [hc, if_pos hm, norm_mul]
          rw [Complex.norm_natCast_cpow_of_pos]
          · simpa using DirichletCharacter.norm_le_one χ _
          · exact_mod_cast hM.trans_le (hJ'sub hm).1
        · exact absurd ⟨hm, h2⟩ h3
        · positivity
        · simp
      · have hc0 : c m = 0 := by simp [hc, hm]
        split_ifs <;> simp [hc0]
    · exact le_rfl
  calc ‖X‖ = ‖Y + (X - Y)‖ := by rw [add_sub_cancel]
    _ ≤ ‖Y‖ + ‖X - Y‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hY (hdec.trans hE)

/-! ## The weight `1/log m` -/

open Classical in
/-- Partial summation for `1/log m`: `1/log y = 1/log M - (1/log M - 1/log y)`, the second
piece monotone and bounded by `1/log M`. -/
lemma log_weight {M : ℝ} (hM : 1 < M) (S : Finset ℕ) {J : Set ℝ} (hJ : J.OrdConnected)
    (hJsub : J ⊆ Icc M (2 * M)) (c : ℕ → ℂ) (ε : ℝ)
    (h : ∀ J' : Set ℝ, J'.OrdConnected → J' ⊆ J →
      ‖∑ m ∈ S, (if (m : ℝ) ∈ J' then c m else 0)‖ ≤ ε) :
    ‖∑ m ∈ S, (if (m : ℝ) ∈ J then c m / ((log m : ℝ) : ℂ) else 0)‖ ≤ 2 * ε / log M := by
  have hlM : 0 < log M := log_pos hM
  set φ : ℝ → ℝ := fun y => 1 / log M - 1 / log y with hφ
  have hlogy : ∀ y ∈ Icc M (2 * M), log M ≤ log y := fun y hy =>
    log_le_log (by linarith) hy.1
  have hφmono : MonotoneOn φ (Icc M (2 * M)) := by
    intro y₁ hy₁ y₂ hy₂ h12
    simp only [hφ]
    have h1 := hlogy y₁ hy₁
    have h2 : log y₁ ≤ log y₂ := log_le_log (by linarith [hy₁.1]) h12
    have : 1 / log y₂ ≤ 1 / log y₁ := one_div_le_one_div_of_le (by linarith) h2
    linarith
  have hφ0 : ∀ y ∈ J, 0 ≤ φ y := by
    intro y hy
    simp only [hφ, sub_nonneg]
    exact one_div_le_one_div_of_le hlM (hlogy y (hJsub hy))
  have hφΨ : ∀ y ∈ J, φ y ≤ 1 / log M := by
    intro y hy
    simp only [hφ]
    have h1 := hlogy y (hJsub hy)
    have : 0 ≤ 1 / log y := one_div_nonneg.2 (by linarith)
    linarith
  have hP := A106R.layer_cake_sum S hJ hJsub hφmono (by positivity) hφ0 hφΨ c 0 ε
    (fun J' hJ' hsub => by rw [zero_mul, sub_zero]; exact h J' hJ' hsub)
  rw [zero_mul, sub_zero] at hP
  have hsplit : (∑ m ∈ S, (if (m : ℝ) ∈ J then c m / ((log m : ℝ) : ℂ) else 0)) =
      ((1 / log M : ℝ) : ℂ) * (∑ m ∈ S, (if (m : ℝ) ∈ J then c m else 0)) -
        ∑ m ∈ S, (if (m : ℝ) ∈ J then c m * (φ m : ℂ) else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : (m : ℝ) ∈ J
    · have hlm : log (m : ℝ) ≠ 0 := by
        have := hlogy _ (hJsub hm); linarith
      have hlmC : ((log (m : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlm
      have hlMC : ((log M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlM.ne'
      rw [if_pos hm, if_pos hm, if_pos hm, hφ]
      push_cast
      field_simp
      ring
    · simp [hm]
  rw [hsplit]
  have h1 : ‖((1 / log M : ℝ) : ℂ) * (∑ m ∈ S, (if (m : ℝ) ∈ J then c m else 0))‖ ≤
      1 / log M * ε := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (h J hJ subset_rfl) (by positivity)
  calc _ ≤ 1 / log M * ε + 1 / log M * ε := (norm_sub_le _ _).trans (add_le_add h1 hP)
    _ = 2 * ε / log M := by ring

/-! ## Divisor sums -/

open Classical in
lemma trunc_sum_le (W M : ℝ) (hM : 0 ≤ M) (n : ℕ) :
    ∑ S ∈ (Pset W).powerset, (if S.card = n then M / ((∏ p ∈ S, p : ℕ) : ℝ) + 1 else 0) ≤
      M * ((1 / 2) ^ n * exp (-(2 * log (mertensProduct W)))) +
        ((Pset W).card + 1 : ℝ) ^ n := by
  have hsplit : (∑ S ∈ (Pset W).powerset,
      (if S.card = n then M / ((∏ p ∈ S, p : ℕ) : ℝ) + 1 else 0)) =
      M * ∑ S ∈ (Pset W).powerset, (if S.card = n then 1 / ((∏ p ∈ S, p : ℕ) : ℝ) else 0) +
        ∑ S ∈ (Pset W).powerset, (if S.card = n then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    split_ifs <;> ring
  rw [hsplit]
  refine add_le_add (mul_le_mul_of_nonneg_left (sum_card_inv_le W n) hM) ?_
  refine le_trans (Finset.sum_le_sum fun S _ => ?_) (A106S.card_powerset_le (Pset W) n)
  split_ifs with h1 h2 <;> first | exact le_rfl | (exact absurd h1.le h2) | norm_num

open Classical in
lemma main_sum_small (W M : ℝ) (n k : ℕ) (hk : 0 < k) (u : ℝ) (hu : u ≠ 0) :
    ∑ S ∈ (Pset W).powerset, (if S.card < n then
      (k : ℝ) * (5 * (M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (k * |u|) + 2 * |u|) else 0) =
      5 * M / |u| * ∑ S ∈ (Pset W).powerset,
        (if S.card < n then 1 / ((∏ p ∈ S, p : ℕ) : ℝ) else 0) +
      2 * k * |u| * ∑ S ∈ (Pset W).powerset, (if S.card < n then (1 : ℝ) else 0) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hu' : |u| ≠ 0 := abs_ne_zero.2 hu
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hd : ((∏ p ∈ S, p : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (prod_pos S (Finset.mem_powerset.1 hS)).ne'
  split_ifs
  · field_simp
  · ring

lemma card_lt_le (W : ℝ) (n : ℕ) :
    ∑ S ∈ (Pset W).powerset, (if S.card < n then (1 : ℝ) else 0) ≤
      ((Pset W).card + 1 : ℝ) ^ n := by
  refine le_trans (Finset.sum_le_sum fun S _ => ?_) (A106S.card_powerset_le (Pset W) n)
  split_ifs with h1 h2 <;> first | exact le_rfl | (exact absurd h1.le h2) | norm_num

/-! ## The two frequency ranges on a subinterval -/

lemma divisor_le {W : ℝ} (hW : 1 ≤ W) {n : ℕ} {S : Finset ℕ} (hS : S ∈ (Pset W).powerset)
    (hSn : S.card < n) : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ W ^ n :=
  (prod_le_pow hW (Finset.mem_powerset.1 hS)).trans (pow_le_pow_right₀ hW hSn.le)

open Classical in
/-- `1 ≤ |u| ≤ T*`: (5.7) on every progression. -/
lemma eps_small {W M : ℝ} (hW : 1 ≤ W) (hM : 0 < M) {k : ℕ} (hk : 0 < k)
    (χ : DirichletCharacter ℂ k) (u : ℝ) (hu : u ≠ 0) (n : ℕ) (hkM : (k : ℝ) * W ^ n ≤ M)
    (J' : Set ℝ) (hJ' : J'.OrdConnected) (hJ'sub : J' ⊆ Icc M (2 * M)) :
    ‖∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
        (if (m : ℝ) ∈ J' ∧ IsRough W m then χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * u) else 0)‖ ≤
      5 * M / |u| * exp (-(1 * log (mertensProduct W))) +
        2 * k * |u| * ((Pset W).card + 1 : ℝ) ^ n +
        (M * ((1 / 2) ^ n * exp (-(2 * log (mertensProduct W)))) +
          ((Pset W).card + 1 : ℝ) ^ n) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hcore := core_bound (W := W) (by linarith) hM hk χ u n J' hJ'sub
    (fun d => 5 * (M / d) / (k * |u|) + 2 * |u|) (fun S hS hSn b => by
      have hd := prod_pos S (Finset.mem_powerset.1 hS)
      have hdpos : (0 : ℝ) < ((∏ p ∈ S, p : ℕ) : ℝ) := by exact_mod_cast hd
      have hdle := divisor_le hW hS hSn
      have hqN : (k : ℝ) ≤ M / ((∏ p ∈ S, p : ℕ) : ℝ) := by
        rw [le_div_iff₀ hdpos]
        exact (mul_le_mul_of_nonneg_left hdle hkpos.le).trans hkM
      exact A106S.prog_sum_bound u hu k hk _ hqN _ (A106S.scaleSet_ordConnected _ J' hJ')
        (A106S.scaleSet_subset _ hd J' M hJ'sub) b)
  refine hcore.trans (add_le_add ?_ (trunc_sum_le W M hM.le n))
  rw [main_sum_small W M n k hk u hu]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (sum_trunc_inv_le W n) (by positivity))
    (mul_le_mul_of_nonneg_left (card_lt_le W n) (by positivity))

open Classical in
/-- `|u| > T*`: the logarithmic-phase bound on every progression. -/
lemma eps_large {W M : ℝ} (hW : 1 ≤ W) (hM : 0 < M) {k : ℕ} (hk : 0 < k)
    (χ : DirichletCharacter ℂ k) (u : ℝ) (n : ℕ) (T Klp E : ℝ) (hT : 0 < T) (hE : 0 ≤ E)
    (hTM : T * W ^ n ≤ M)
    (hLP : ∀ N : ℝ, T ≤ N → N ≤ M → ∀ a : ℕ, ∀ I : Set ℝ, I.OrdConnected →
      I ⊆ Icc N (2 * N) →
      ‖∑ t ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter (fun t => t ≡ a [MOD k]),
          (if (t : ℝ) ∈ I then (t : ℂ) ^ (Complex.I * u) else 0)‖ ≤ Klp * (N / k) * E)
    (J' : Set ℝ) (hJ' : J'.OrdConnected) (hJ'sub : J' ⊆ Icc M (2 * M)) :
    ‖∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
        (if (m : ℝ) ∈ J' ∧ IsRough W m then χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * u) else 0)‖ ≤
      |Klp| * M * E * exp (-(1 * log (mertensProduct W))) +
        (M * ((1 / 2) ^ n * exp (-(2 * log (mertensProduct W)))) +
          ((Pset W).card + 1 : ℝ) ^ n) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hcore := core_bound (W := W) (by linarith) hM hk χ u n J' hJ'sub
    (fun d => |Klp| * ((M / d) / k) * E) (fun S hS hSn b => by
      have hd := prod_pos S (Finset.mem_powerset.1 hS)
      have hdpos : (0 : ℝ) < ((∏ p ∈ S, p : ℕ) : ℝ) := by exact_mod_cast hd
      have hd1 : (1 : ℝ) ≤ ((∏ p ∈ S, p : ℕ) : ℝ) := by exact_mod_cast hd
      have hdle := divisor_le hW hS hSn
      have hTN : T ≤ M / ((∏ p ∈ S, p : ℕ) : ℝ) := by
        rw [le_div_iff₀ hdpos]
        exact (mul_le_mul_of_nonneg_left hdle hT.le).trans hTM
      have hNM : M / ((∏ p ∈ S, p : ℕ) : ℝ) ≤ M := div_le_self hM.le hd1
      refine (hLP _ hTN hNM b _ (A106S.scaleSet_ordConnected _ J' hJ')
        (A106S.scaleSet_subset _ hd J' M hJ'sub)).trans ?_
      have : 0 ≤ M / ((∏ p ∈ S, p : ℕ) : ℝ) / k := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) this) hE)
  refine hcore.trans (add_le_add ?_ (trunc_sum_le W M hM.le n))
  have he : (∑ S ∈ (Pset W).powerset, (if S.card < n then
      (k : ℝ) * (|Klp| * ((M / ((∏ p ∈ S, p : ℕ) : ℝ)) / k) * E) else 0)) =
      |Klp| * M * E * ∑ S ∈ (Pset W).powerset,
        (if S.card < n then 1 / ((∏ p ∈ S, p : ℕ) : ℝ) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hd : ((∏ p ∈ S, p : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (prod_pos S (Finset.mem_powerset.1 hS)).ne'
    split_ifs
    · field_simp
    · ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (sum_trunc_inv_le W n) (by positivity)

/-! ## Mertens and the final arithmetic -/

lemma ev_mertens : ∀ᶠ x in atTop, 0 < mertensProduct (sieveLevel x) ∧
    exp (-eulerMascheroniConstant) / 2 ≤ log x * mertensProduct (sieveLevel x) := by
  have hW : Tendsto sieveLevel atTop atTop := by
    show Tendsto (fun x => exp (log x ^ (0.24 : ℝ))) atTop atTop
    exact tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop)
  have h := mertens_product.comp hW
  have hpos : 0 < exp (-eulerMascheroniConstant) := exp_pos _
  have h1 := h.eventually (lt_mem_nhds (half_lt_self hpos))
  filter_upwards [h1, eventually_ge_atTop (exp 1)] with x hx hx1
  have hlW : log (sieveLevel x) = log x ^ (0.24 : ℝ) := log_exp _
  simp only [Function.comp] at hx
  rw [hlW] at hx
  have hL1 : 1 ≤ log x := by
    rw [← log_exp 1]; exact log_le_log (exp_pos 1) hx1
  have hr0 : 0 < log x ^ (0.24 : ℝ) := rpow_pos_of_pos (by linarith) _
  have hrL : log x ^ (0.24 : ℝ) ≤ log x := by
    calc log x ^ (0.24 : ℝ) ≤ log x ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = log x := rpow_one _
  set V := mertensProduct (sieveLevel x)
  have hV : 0 < V := by
    by_contra hcon
    push Not at hcon
    have := mul_nonpos_of_nonpos_of_nonneg hcon hr0.le
    linarith
  refine ⟨hV, ?_⟩
  have : V * log x ^ (0.24 : ℝ) ≤ log x * V := by
    rw [mul_comm (log x)]; exact mul_le_mul_of_nonneg_left hrL hV.le
  linarith

lemma pre_step {M V L cV w lM ε : ℝ} (hM : 0 < M) (hV : 0 < V) (hcV : 0 < cV)
    (hLV : cV ≤ L * V) (hL : 0 < L) (hw : 0 < w) (hlM : w * L ≤ lM) (hε : 0 ≤ ε) :
    1 / (M * V) * (2 * ε / lM) ≤ 2 / (cV * w) * (ε / M) := by
  have h1 : 1 / V ≤ L / cV := by rw [div_le_div_iff₀ hV hcV]; linarith
  have h2 : 2 * ε / lM ≤ 2 * ε / (w * L) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hlM
  calc 1 / (M * V) * (2 * ε / lM) = 1 / M * (1 / V) * (2 * ε / lM) := by
        rw [one_div_mul_one_div]
    _ ≤ 1 / M * (L / cV) * (2 * ε / (w * L)) := by
        have hlM0 : 0 < lM := lt_of_lt_of_le (by positivity) hlM
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
          (div_nonneg (by positivity) hlM0.le) (by positivity)
    _ = 2 / (cV * w) * (ε / M) := by field_simp

lemma inv_V_bounds {V L cV : ℝ} (hV : 0 < V) (hcV : 0 < cV) (hLV : cV ≤ L * V) :
    exp (-(1 * log V)) ≤ L / cV ∧ exp (-(2 * log V)) ≤ (L / cV) ^ 2 := by
  have h1 : V⁻¹ ≤ L / cV := by rw [← one_div, div_le_div_iff₀ hV hcV]; linarith
  have e1 : exp (-(1 * log V)) = V⁻¹ := by rw [one_mul, Real.exp_neg, Real.exp_log hV]
  have e2 : exp (-(2 * log V)) = V⁻¹ ^ 2 := by
    rw [Real.exp_neg, show (2 : ℝ) * log V = ((2 : ℕ) : ℝ) * log V by norm_num,
      Real.exp_nat_mul, Real.exp_log hV, inv_pow]
  refine ⟨e1 ▸ h1, e2 ▸ pow_le_pow_left₀ (by positivity) h1 2⟩

lemma small_div {M V L x cV w k u A₀ A₄ Tst Q P' : ℝ} {n : ℕ} (hM : 0 < M) (hV : 0 < V)
    (hcV : 0 < cV) (hLV : cV ≤ L * V) (hL1 : 1 ≤ L) (hx : 0 < x) (hMx : x ^ w ≤ M)
    (hA₀ : 0 ≤ A₀) (_hk0 : 0 ≤ k) (hk : k ≤ L ^ A₀) (hu : 0 < |u|) (huT : |u| ≤ Tst)
    (hT1 : 1 ≤ Tst) (hP'0 : 0 ≤ P') (hP' : P' ≤ Q) (hn : (1 / 2 : ℝ) ^ n ≤ L ^ (-(A₄ + 2)))
    (hQ : L ^ A₀ * Tst * Q ≤ x ^ (w / 2)) (hA₄ : L ^ A₄ ≤ x ^ (w / 2)) :
    (5 * M / |u| * exp (-(1 * log V)) + 2 * k * |u| * P' +
        (M * ((1 / 2) ^ n * exp (-(2 * log V))) + P')) / M ≤
      (5 / cV + 3 + 1 / cV ^ 2) * (L ^ (-A₄) + L ^ (1 : ℝ) * (|u|⁻¹ + x ^ (-(w / 2)))) := by
  have hL0 : 0 < L := by linarith
  obtain ⟨hΛ1, hΛ2⟩ := inv_V_bounds hV hcV hLV
  have hxw : 0 < x ^ (w / 2) := rpow_pos_of_pos hx _
  have hx2 : x ^ w = x ^ (w / 2) * x ^ (w / 2) := by rw [← rpow_add hx]; ring_nf
  have hneg : x ^ (-(w / 2)) = (x ^ (w / 2))⁻¹ := rpow_neg hx.le _
  have hLA : L ^ (-A₄) = (L ^ A₄)⁻¹ := rpow_neg hL0.le _
  have hLApos : 0 < L ^ A₄ := rpow_pos_of_pos hL0 _
  have hxA : x ^ (-(w / 2)) ≤ L ^ (-A₄) := by
    rw [hneg, hLA]; exact inv_anti₀ hLApos hA₄
  have hLA₀ : 1 ≤ L ^ A₀ := one_le_rpow hL1 hA₀
  have hQ0 : 0 ≤ Q := hP'0.trans hP'
  have hQx : Q ≤ x ^ (w / 2) := by
    refine le_trans ?_ hQ
    have : 1 ≤ L ^ A₀ * Tst := one_le_mul_of_one_le_of_one_le hLA₀ hT1
    nlinarith
  have hMinv : x ^ (w / 2) / M ≤ x ^ (-(w / 2)) := by
    rw [div_le_iff₀ hM, hneg]
    calc x ^ (w / 2) = (x ^ (w / 2))⁻¹ * (x ^ (w / 2) * x ^ (w / 2)) := by field_simp
      _ ≤ (x ^ (w / 2))⁻¹ * M := by rw [← hx2]; gcongr
  have hx0' : 0 ≤ x ^ (-(w / 2)) := by rw [hneg]; positivity
  set a := L ^ (-A₄)
  set b := L * |u|⁻¹
  set c := L * x ^ (-(w / 2))
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hc : 0 ≤ c := by positivity
  have t1 : 5 * M / |u| * exp (-(1 * log V)) / M ≤ 5 / cV * b := by
    calc 5 * M / |u| * exp (-(1 * log V)) / M = 5 / |u| * exp (-(1 * log V)) := by
          field_simp
      _ ≤ 5 / |u| * (L / cV) := by gcongr
      _ = 5 / cV * b := by simp only [b]; field_simp
  have t2 : 2 * k * |u| * P' / M ≤ 2 * c := by
    have h1 : k * |u| * P' ≤ L ^ A₀ * Tst * Q :=
      mul_le_mul (mul_le_mul hk huT hu.le (by positivity)) hP' hP'0 (by positivity)
    have h2 : 2 * k * |u| * P' / M ≤ 2 * (x ^ (w / 2) / M) := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hM]; nlinarith
    have h3 : x ^ (-(w / 2)) ≤ c := by
      simp only [c]; nlinarith
    linarith
  have t3 : M * ((1 / 2) ^ n * exp (-(2 * log V))) / M ≤ 1 / cV ^ 2 * a := by
    have e : L ^ (-(A₄ + 2)) = a / L ^ 2 := by
      rw [show -(A₄ + 2) = -A₄ - 2 by ring, rpow_sub hL0, rpow_two]
    calc M * ((1 / 2) ^ n * exp (-(2 * log V))) / M = (1 / 2) ^ n * exp (-(2 * log V)) := by
          field_simp
      _ ≤ a / L ^ 2 * (L / cV) ^ 2 := by
          rw [← e]; exact mul_le_mul hn hΛ2 (by positivity) (by positivity)
      _ = 1 / cV ^ 2 * a := by field_simp
  have t4 : P' / M ≤ a := by
    calc P' / M ≤ x ^ (w / 2) / M := div_le_div_of_nonneg_right (hP'.trans hQx) hM.le
      _ ≤ x ^ (-(w / 2)) := hMinv
      _ ≤ a := hxA
  have hsplit : (5 * M / |u| * exp (-(1 * log V)) + 2 * k * |u| * P' +
      (M * ((1 / 2) ^ n * exp (-(2 * log V))) + P')) / M =
      5 * M / |u| * exp (-(1 * log V)) / M + 2 * k * |u| * P' / M +
        M * ((1 / 2) ^ n * exp (-(2 * log V))) / M + P' / M := by ring
  have hR : L ^ (1 : ℝ) * (|u|⁻¹ + x ^ (-(w / 2))) = b + c := by
    rw [rpow_one]; ring
  rw [hsplit, hR]
  have expand : (5 / cV + 3 + 1 / cV ^ 2) * (a + (b + c)) =
      5 / cV * a + 5 / cV * b + 5 / cV * c + 3 * a + 3 * b + 3 * c +
        1 / cV ^ 2 * a + 1 / cV ^ 2 * b + 1 / cV ^ 2 * c := by ring
  have p1 : 0 ≤ 5 / cV * a := by positivity
  have p2 : 0 ≤ 5 / cV * c := by positivity
  have p3 : 0 ≤ 1 / cV ^ 2 * b := by positivity
  have p4 : 0 ≤ 1 / cV ^ 2 * c := by positivity
  rw [expand]
  linarith

lemma large_div {M V L x cV w A₄ Q P' Klp E : ℝ} {n : ℕ} (hM : 0 < M) (hV : 0 < V)
    (hcV : 0 < cV) (hLV : cV ≤ L * V) (hL1 : 1 ≤ L) (hx : 0 < x) (hMx : x ^ w ≤ M)
    (hE : 0 ≤ E) (_hP'0 : 0 ≤ P') (hP' : P' ≤ Q) (hn : (1 / 2 : ℝ) ^ n ≤ L ^ (-(A₄ + 2)))
    (hQx : Q ≤ x ^ (w / 2)) (hA₄ : L ^ A₄ ≤ x ^ (w / 2)) :
    (|Klp| * M * E * exp (-(1 * log V)) +
        (M * ((1 / 2) ^ n * exp (-(2 * log V))) + P')) / M ≤
      (|Klp| / cV + 1 + 1 / cV ^ 2) * (L ^ (-A₄) + L ^ (1 : ℝ) * E) := by
  have hL0 : 0 < L := by linarith
  obtain ⟨hΛ1, hΛ2⟩ := inv_V_bounds hV hcV hLV
  have hxw : 0 < x ^ (w / 2) := rpow_pos_of_pos hx _
  have hx2 : x ^ w = x ^ (w / 2) * x ^ (w / 2) := by rw [← rpow_add hx]; ring_nf
  have hneg : x ^ (-(w / 2)) = (x ^ (w / 2))⁻¹ := rpow_neg hx.le _
  have hLA : L ^ (-A₄) = (L ^ A₄)⁻¹ := rpow_neg hL0.le _
  have hLApos : 0 < L ^ A₄ := rpow_pos_of_pos hL0 _
  have hxA : x ^ (-(w / 2)) ≤ L ^ (-A₄) := by
    rw [hneg, hLA]; exact inv_anti₀ hLApos hA₄
  have hMinv : x ^ (w / 2) / M ≤ x ^ (-(w / 2)) := by
    rw [div_le_iff₀ hM, hneg]
    calc x ^ (w / 2) = (x ^ (w / 2))⁻¹ * (x ^ (w / 2) * x ^ (w / 2)) := by field_simp
      _ ≤ (x ^ (w / 2))⁻¹ * M := by rw [← hx2]; gcongr
  set a := L ^ (-A₄)
  have ha : 0 ≤ a := by positivity
  have t1 : |Klp| * M * E * exp (-(1 * log V)) / M ≤ |Klp| / cV * (L * E) := by
    calc |Klp| * M * E * exp (-(1 * log V)) / M = |Klp| * E * exp (-(1 * log V)) := by
          field_simp
      _ ≤ |Klp| * E * (L / cV) := by gcongr
      _ = |Klp| / cV * (L * E) := by field_simp
  have t3 : M * ((1 / 2) ^ n * exp (-(2 * log V))) / M ≤ 1 / cV ^ 2 * a := by
    have e : L ^ (-(A₄ + 2)) = a / L ^ 2 := by
      rw [show -(A₄ + 2) = -A₄ - 2 by ring, rpow_sub hL0, rpow_two]
    calc M * ((1 / 2) ^ n * exp (-(2 * log V))) / M = (1 / 2) ^ n * exp (-(2 * log V)) := by
          field_simp
      _ ≤ a / L ^ 2 * (L / cV) ^ 2 := by
          rw [← e]; exact mul_le_mul hn hΛ2 (by positivity) (by positivity)
      _ = 1 / cV ^ 2 * a := by field_simp
  have t4 : P' / M ≤ a := by
    calc P' / M ≤ x ^ (w / 2) / M := div_le_div_of_nonneg_right (hP'.trans hQx) hM.le
      _ ≤ x ^ (-(w / 2)) := hMinv
      _ ≤ a := hxA
  have hsplit : (|Klp| * M * E * exp (-(1 * log V)) +
      (M * ((1 / 2) ^ n * exp (-(2 * log V))) + P')) / M =
      |Klp| * M * E * exp (-(1 * log V)) / M +
        M * ((1 / 2) ^ n * exp (-(2 * log V))) / M + P' / M := by ring
  rw [hsplit, rpow_one]
  have hLE : 0 ≤ L * E := by positivity
  have expand : (|Klp| / cV + 1 + 1 / cV ^ 2) * (a + L * E) =
      |Klp| / cV * a + |Klp| / cV * (L * E) + a + L * E + 1 / cV ^ 2 * a +
        1 / cV ^ 2 * (L * E) := by ring
  have p1 : 0 ≤ |Klp| / cV * a := by positivity
  have p2 : 0 ≤ 1 / cV ^ 2 * (L * E) := by positivity
  rw [expand]
  linarith

end ArtinPrimitiveRoots.A106T

namespace ArtinPrimitiveRoots.A106T

open Real Set Filter Topology

lemma K_le_small (Klp c : ℝ) (hc : 0 < c) :
    5 / c + 3 + 1 / c ^ 2 ≤ 5 / c + 3 + 1 / c ^ 2 + |Klp| / c := by
  have : 0 ≤ |Klp| / c := by positivity
  linarith

lemma K_le_large (Klp c : ℝ) (hc : 0 < c) :
    |Klp| / c + 1 + 1 / c ^ 2 ≤ 5 / c + 3 + 1 / c ^ 2 + |Klp| / c := by
  have : 0 ≤ 5 / c := by positivity
  linarith

lemma combine_le {A B X c : ℝ} (hc : 0 ≤ c) (hX : 0 ≤ X) (hAB : A ≤ B) :
    c * (A * X) ≤ c * (B * X) :=
  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAB hX) hc

open Classical in
/-- (10.19) at a fixed large `x`, given the growth conditions and the logarithmic-phase bound. -/
lemma main_x {x M wMinus wPlus A₀ A₄ C₃ Klp cV : ℝ} {k : ℕ} (χ : DirichletCharacter ℂ k)
    (J : Set ℝ) (u : ℝ) (hx0 : 0 < x) (hL2 : 2 ≤ log x)
    (hV : 0 < mertensProduct (sieveLevel x)) (hcV : 0 < cV)
    (hLV : cV ≤ log x * mertensProduct (sieveLevel x))
    (hn : (1 / 2 : ℝ) ^ ⌈log x ^ (0.1 : ℝ)⌉₊ ≤ log x ^ (-(A₄ + 2)))
    (hQ : log x ^ A₀ * exp (log x / log (log x) ^ 2) *
      (sieveLevel x + 2) ^ ⌈log x ^ (0.1 : ℝ)⌉₊ ≤ x ^ (wMinus / 2))
    (hA₄x : log x ^ A₄ ≤ x ^ (wMinus / 2))
    (hlp : ∀ N : ℝ, exp (log x / log (log x) ^ 2) ≤ N → N ≤ 2 * x ^ 5 →
      ∀ v : ℝ, exp (log x / (2 * log (log x) ^ 2)) ≤ |v| → |v| ≤ 4 * x ^ 3 →
      ∀ a : ℕ, ∀ I : Set ℝ, I.OrdConnected → I ⊆ Set.Icc N (2 * N) →
        ‖∑ n ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter (fun n => n ≡ a [MOD k]),
            (if (n : ℝ) ∈ I then (n : ℂ) ^ (Complex.I * v) else 0)‖ ≤
          Klp * (N / k) * exp (-(log x / log (log x) ^ C₃)))
    (hw0 : 0 < wMinus) (hww : wMinus < wPlus) (hw1 : wPlus < 1) (hA₀ : 0 < A₀)
    (hM : 0 < M) (hM1 : wMinus ≤ log M / log x) (hM2 : log (2 * M) / log x ≤ wPlus)
    (hk : 0 < k) (hkA : (k : ℝ) ≤ log x ^ A₀) (hJ : J.OrdConnected)
    (hJsub : J ⊆ Set.Icc M (2 * M)) (hu1 : 1 ≤ |u|) (hu2 : |u| < x ^ 2) :
    ‖((1 / (M * mertensProduct (sieveLevel x)) : ℝ) : ℂ) *
        ∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
          (if (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m then
            χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * u) / ((log m : ℝ) : ℂ) else 0)‖ ≤
      2 / (cV * wMinus) * (5 / cV + 3 + 1 / cV ^ 2 + |Klp| / cV) *
        (log x ^ (-A₄) +
          if |u| ≤ exp (log x / log (log x) ^ 2) then
            log x ^ (1 : ℝ) * (|u|⁻¹ + x ^ (-(wMinus / 2)))
          else log x ^ (1 : ℝ) * exp (-(log x / log (log x) ^ C₃))) := by
  set L := log x with hLdef
  set W := sieveLevel x with hWdef
  set V := mertensProduct W with hVdef
  set n := ⌈L ^ (0.1 : ℝ)⌉₊ with hndef
  set Tst := exp (L / log L ^ 2) with hTst
  set Q := (W + 2) ^ n with hQdef
  set P' := ((Pset W).card + 1 : ℝ) ^ n with hP'def
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hW1 : 1 ≤ W := by
    rw [hWdef]; unfold sieveLevel; exact Real.one_le_exp (by positivity)
  have hlogM : wMinus * L ≤ log M := (le_div_iff₀ hL0).1 hM1
  have hM1' : 1 < M := (log_pos_iff hM.le).1 (by nlinarith)
  have hMx : x ^ wMinus ≤ M := by
    rw [rpow_def_of_pos hx0, ← Real.exp_log hM]
    exact Real.exp_le_exp.2 (by rw [← hLdef]; linarith)
  have hMle : M ≤ x := by
    have h2 : log (2 * M) ≤ wPlus * L := (div_le_iff₀ hL0).1 hM2
    have h3 : log (2 * M) ≤ log x := by nlinarith
    have := (log_le_log_iff (by linarith) hx0).1 h3
    linarith
  have hx1 : 1 ≤ x := by linarith
  have hP'0 : 0 ≤ P' := by positivity
  have hP'Q : P' ≤ Q := pow_le_pow_left₀ (by positivity)
    (by have := card_Pset_le (W := W) (by linarith); linarith) n
  have hT1 : 1 ≤ Tst := Real.one_le_exp (by positivity)
  have hLA₀ : 1 ≤ L ^ A₀ := one_le_rpow hL1 hA₀.le
  have hWQ : W ^ n ≤ Q := pow_le_pow_left₀ (by linarith) (by linarith) n
  have hxw : x ^ (wMinus / 2) ≤ x ^ wMinus := rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hWn0 : 0 ≤ W ^ n := by positivity
  have hkM : (k : ℝ) * W ^ n ≤ M := by
    calc (k : ℝ) * W ^ n ≤ L ^ A₀ * Tst * Q := by
          have : (k : ℝ) ≤ L ^ A₀ * Tst :=
            hkA.trans (le_mul_of_one_le_right (by positivity) hT1)
          exact mul_le_mul this hWQ hWn0 (by positivity)
      _ ≤ M := hQ.trans (hxw.trans hMx)
  have hTM : Tst * W ^ n ≤ M := by
    calc Tst * W ^ n ≤ L ^ A₀ * Tst * Q := by
          have : Tst ≤ L ^ A₀ * Tst := le_mul_of_one_le_left (by positivity) hLA₀
          exact mul_le_mul this hWQ hWn0 (by positivity)
      _ ≤ M := hQ.trans (hxw.trans hMx)
  -- rewrite the sum with a coefficient and the weight `1/log m`
  set c : ℕ → ℂ := fun m => if IsRough W m then χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * u)
    else 0 with hc
  have hsum : (∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
      (if (m : ℝ) ∈ J ∧ IsRough W m then
        χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * u) / ((log m : ℝ) : ℂ) else 0)) =
      ∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
        (if (m : ℝ) ∈ J then c m / ((log m : ℝ) : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h1 : (m : ℝ) ∈ J <;> by_cases h2 : IsRough W m <;> simp [hc, h1, h2]
  have hcJ : ∀ J' : Set ℝ, (∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
      (if (m : ℝ) ∈ J' then c m else 0)) =
      ∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1), (if (m : ℝ) ∈ J' ∧ IsRough W m then
        χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * u) else 0) := by
    intro J'
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h1 : (m : ℝ) ∈ J' <;> by_cases h2 : IsRough W m <;> simp [hc, h1, h2]
  rw [hsum, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hK : 0 ≤ 2 / (cV * wMinus) := by positivity
  have hu0 : u ≠ 0 := by intro h; rw [h, abs_zero] at hu1; linarith
  by_cases hT : |u| ≤ Tst
  · rw [if_pos hT]
    set ε := 5 * M / |u| * exp (-(1 * log V)) + 2 * k * |u| * P' +
      (M * ((1 / 2) ^ n * exp (-(2 * log V))) + P') with hε
    have hε0 : 0 ≤ ε := by positivity
    have hlw := log_weight hM1' (Finset.range (⌊2 * M⌋₊ + 1)) hJ hJsub c ε (fun J' hJ' hsub => by
      rw [hcJ J']
      exact eps_small hW1 hM hk χ u hu0 n hkM J' hJ' (hsub.trans hJsub))
    have hdiv := small_div hM hV hcV hLV hL1 hx0 hMx hA₀.le (Nat.cast_nonneg k) hkA
      (by positivity) hT hT1 hP'0 hP'Q hn hQ hA₄x
    have hX : 0 ≤ L ^ (-A₄) + L ^ (1 : ℝ) * (|u|⁻¹ + x ^ (-(wMinus / 2))) := by positivity
    calc 1 / (M * V) * ‖_‖ ≤ 1 / (M * V) * (2 * ε / log M) :=
          mul_le_mul_of_nonneg_left hlw (by positivity)
      _ ≤ 2 / (cV * wMinus) * (ε / M) := pre_step hM hV hcV hLV hL0 hw0 hlogM hε0
      _ ≤ 2 / (cV * wMinus) * ((5 / cV + 3 + 1 / cV ^ 2) *
            (L ^ (-A₄) + L ^ (1 : ℝ) * (|u|⁻¹ + x ^ (-(wMinus / 2))))) :=
          mul_le_mul_of_nonneg_left hdiv hK
      _ ≤ 2 / (cV * wMinus) * ((5 / cV + 3 + 1 / cV ^ 2 + |Klp| / cV) *
            (L ^ (-A₄) + L ^ (1 : ℝ) * (|u|⁻¹ + x ^ (-(wMinus / 2))))) :=
          combine_le hK hX (K_le_small Klp cV hcV)
      _ = _ := by ring
  · rw [if_neg hT]
    push Not at hT
    set E := exp (-(L / log L ^ C₃)) with hE
    set ε := |Klp| * M * E * exp (-(1 * log V)) +
      (M * ((1 / 2) ^ n * exp (-(2 * log V))) + P') with hε
    have hε0 : 0 ≤ ε := by positivity
    have hlogL : 0 < log L := log_pos (by linarith)
    have hv1 : exp (L / (2 * log L ^ 2)) ≤ |u| := by
      refine le_trans (Real.exp_le_exp.2 ?_) hT.le
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    have hv2 : |u| ≤ 4 * x ^ 3 := by
      have h1 : x ^ 2 ≤ x ^ 3 := pow_le_pow_right₀ hx1 (by norm_num)
      have h2 : 0 ≤ x ^ 3 := by positivity
      linarith
    have hLP : ∀ N : ℝ, Tst ≤ N → N ≤ M → ∀ a : ℕ, ∀ I : Set ℝ, I.OrdConnected →
        I ⊆ Icc N (2 * N) →
        ‖∑ t ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter (fun t => t ≡ a [MOD k]),
            (if (t : ℝ) ∈ I then (t : ℂ) ^ (Complex.I * u) else 0)‖ ≤ Klp * (N / k) * E := by
      intro N hTN hNM a I hI hIsub
      have hN2 : N ≤ 2 * x ^ 5 := by
        have h1 : x ^ 1 ≤ x ^ 5 := pow_le_pow_right₀ hx1 (by norm_num)
        have h2 : 0 ≤ x ^ 5 := by positivity
        rw [pow_one] at h1
        linarith
      exact hlp N hTN hN2 u hv1 hv2 a I hI hIsub
    have hlw := log_weight hM1' (Finset.range (⌊2 * M⌋₊ + 1)) hJ hJsub c ε (fun J' hJ' hsub => by
      rw [hcJ J']
      exact eps_large hW1 hM hk χ u n Tst Klp E (Real.exp_pos _) (Real.exp_pos _).le hTM hLP J'
        hJ' (hsub.trans hJsub))
    have hQx : Q ≤ x ^ (wMinus / 2) := by
      refine le_trans ?_ hQ
      have : 1 ≤ L ^ A₀ * Tst := one_le_mul_of_one_le_of_one_le hLA₀ hT1
      have hQ0 : 0 ≤ Q := hP'0.trans hP'Q
      exact le_mul_of_one_le_left hQ0 this
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hdiv := large_div (Klp := Klp) hM hV hcV hLV hL1 hx0 hMx hE0 hP'0 hP'Q hn
      hQx hA₄x
    have hX : 0 ≤ L ^ (-A₄) + L ^ (1 : ℝ) * E :=
      add_nonneg (rpow_nonneg hL0.le _) (mul_nonneg (rpow_nonneg hL0.le _) hE0)
    calc 1 / (M * V) * ‖_‖ ≤ 1 / (M * V) * (2 * ε / log M) :=
          mul_le_mul_of_nonneg_left hlw (by positivity)
      _ ≤ 2 / (cV * wMinus) * (ε / M) := pre_step hM hV hcV hLV hL0 hw0 hlogM hε0
      _ ≤ 2 / (cV * wMinus) * ((|Klp| / cV + 1 + 1 / cV ^ 2) * (L ^ (-A₄) + L ^ (1 : ℝ) * E)) :=
          mul_le_mul_of_nonneg_left hdiv hK
      _ ≤ 2 / (cV * wMinus) * ((5 / cV + 3 + 1 / cV ^ 2 + |Klp| / cV) *
            (L ^ (-A₄) + L ^ (1 : ℝ) * E)) :=
          combine_le hK hX (K_le_large Klp cV hcV)
      _ = _ := by ring

end ArtinPrimitiveRoots.A106T

namespace ArtinPrimitiveRoots

open Real Filter A106T

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real Filter A106T
open Classical in
theorem solution :
    ∃ C₃ : ℝ, 0 < C₃ ∧
    ∀ wMinus wPlus : ℝ, 0 < wMinus → wMinus < wPlus → wPlus < 1 →
    ∀ A₀ : ℝ, 0 < A₀ → ∃ C₀ c₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧
    ∀ A₄ : ℝ, 0 < A₄ → ∃ K x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ M : ℝ, 0 < M → wMinus ≤ log M / log x → log (2 * M) / log x ≤ wPlus →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc M (2 * M) →
      ∀ u : ℝ, 1 ≤ |u| → |u| < x ^ 2 →
        ‖((1 / (M * mertensProduct (sieveLevel x)) : ℝ) : ℂ) *
            ∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
              (if (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m then
                χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * u) / ((log m : ℝ) : ℂ) else 0)‖ ≤
          K * (log x ^ (-A₄) +
            if |u| ≤ exp (log x / log (log x) ^ 2) then
              log x ^ C₀ * (|u|⁻¹ + x ^ (-c₀))
            else log x ^ C₀ * exp (-(log x / log (log x) ^ C₃))) := by
  obtain ⟨C₃, Klp, hC₃, hlp⟩ := log_phase_progression
  refine ⟨C₃, hC₃, fun wMinus wPlus hw0 hww hw1 A₀ hA₀ =>
    ⟨1, wMinus / 2, one_pos, by positivity, fun A₄ hA₄ => ?_⟩⟩
  obtain ⟨xlp, hlp'⟩ := hlp A₀ hA₀
  have hcV : 0 < exp (-eulerMascheroniConstant) / 2 := by positivity
  have hev : ∀ᶠ x in atTop, xlp ≤ x ∧ 0 < x ∧
      (0 < mertensProduct (sieveLevel x) ∧
        exp (-eulerMascheroniConstant) / 2 ≤ log x * mertensProduct (sieveLevel x)) ∧
      (2 ≤ log x ∧
      (1 / 2 : ℝ) ^ ⌈log x ^ (0.1 : ℝ)⌉₊ ≤ log x ^ (-(A₄ + 2)) ∧
      log x ^ A₀ * exp (log x / log (log x) ^ 2) *
          (sieveLevel x + 2) ^ ⌈log x ^ (0.1 : ℝ)⌉₊ ≤ x ^ (wMinus / 2) ∧
      log x ^ A₄ ≤ x ^ (wMinus / 2)) := by
    filter_upwards [eventually_ge_atTop xlp, eventually_gt_atTop (0 : ℝ), ev_mertens,
      ev_x A₀ A₄ wMinus hA₀ hA₄ hw0] with x h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hev
  refine ⟨2 / (exp (-eulerMascheroniConstant) / 2 * wMinus) *
      (5 / (exp (-eulerMascheroniConstant) / 2) + 3 + 1 / (exp (-eulerMascheroniConstant) / 2) ^ 2 +
        |Klp| / (exp (-eulerMascheroniConstant) / 2)), x₀,
    fun x hx M hM hM1 hM2 k hk hkA χ J hJ hJsub u hu1 hu2 => ?_⟩
  obtain ⟨hxlp, hx0, ⟨hV, hLV⟩, hL2, hn, hQ, hA₄x⟩ := hx₀ x hx
  exact main_x χ J u hx0 hL2 hV hcV hLV hn hQ hA₄x
    (fun N h1 h2 v hv1 hv2 a I hI hIsub => hlp' x hxlp N h1 h2 k hk hkA v hv1 hv2 a I hI hIsub)
    hw0 hww hw1 hA₀ hM hM1 hM2 hk hkA hJ hJsub hu1 hu2
end
