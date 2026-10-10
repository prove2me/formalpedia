-- Prove2me | solution 1 for ArtinPrimitiveRoots.rough_factor_coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T13:23:59.731871+00:00
-- url     : https://prove2.me/submissions/ecc630e8-44d6-499f-b00d-71ce46515ebb

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_rough_prime_product_count
import Theorems.Thm_ArtinPrimitiveRoots_rough_count_character
import Theorems.Thm_ArtinPrimitiveRoots_rough_prime_product_high_frequency
import Theorems.Thm_ArtinPrimitiveRoots_rough_twisted_log_weighted_bound
import Theorems.Thm_ArtinPrimitiveRoots_mertens_product

section
/-!
# A monotone decomposition of the rough-number density

The simplex integrand of `D_{γ,j}` is `(w - ∑ x)⁻¹ ∏ (x i)⁻¹`. On the simplex `w - ∑ x ≥ γ`,
so `(w - ∑ x)⁻¹ = γ⁻¹ - (γ⁻¹ - (w - ∑ x)⁻¹)` with both pieces nonnegative. Both resulting
simplex integrals are nondecreasing in `w` (the domain grows with `w`, and the second integrand
grows with `w`). Hence `D_γ = D⁺ - D⁻` on `[γ, (N + 1) γ)` with `D^±` nonnegative and
nondecreasing on all of `ℝ`. This bounded-variation statement replaces the Lipschitz property
of `D_γ` (p. 67) in the partial summations of the proof of Proposition 10.3.
-/

namespace ArtinPrimitiveRoots.A106R

open Real MeasureTheory Set Filter

/-- The simplex region `x i ≥ γ`, `∑ x ≤ w - γ`. -/
def Om (γ w : ℝ) (m : ℕ) : Set (Fin m → ℝ) := {x | (∀ i, γ ≤ x i) ∧ ∑ i, x i ≤ w - γ}

lemma isClosed_Om (γ w : ℝ) (m : ℕ) : IsClosed (Om γ w m) := by
  have h1 : IsClosed {x : Fin m → ℝ | ∀ i, γ ≤ x i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {x : Fin m → ℝ | ∑ i, x i ≤ w - γ} :=
    isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  exact h1.inter h2

lemma measurableSet_Om (γ w : ℝ) (m : ℕ) : MeasurableSet (Om γ w m) :=
  (isClosed_Om γ w m).measurableSet

lemma Om_subset (γ w : ℝ) (hγ : 0 < γ) (m : ℕ) :
    Om γ w m ⊆ Set.pi univ (fun _ => Icc γ w) := by
  intro x hx i _
  refine ⟨hx.1 i, ?_⟩
  have : x i ≤ ∑ j, x j :=
    Finset.single_le_sum (fun j _ => (hγ.le.trans (hx.1 j))) (Finset.mem_univ i)
  linarith [hx.2]

lemma volume_Om_ne_top (γ w : ℝ) (hγ : 0 < γ) (m : ℕ) : volume (Om γ w m) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (Om_subset γ w hγ m))
  exact ((isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top).ne

lemma Om_mono (γ : ℝ) {w w' : ℝ} (h : w ≤ w') (m : ℕ) : Om γ w m ⊆ Om γ w' m :=
  fun _ hx => ⟨hx.1, by linarith [hx.2]⟩

lemma integrableOn_Om {γ w : ℝ} (hγ : 0 < γ) {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (K : ℝ) (hK : ∀ x ∈ Om γ w n, |f x| ≤ K) :
    IntegrableOn f (Om γ w n) := by
  refine Measure.integrableOn_of_bounded (M := K) (volume_Om_ne_top γ w hγ n)
    hf.aestronglyMeasurable ?_
  refine (ae_restrict_iff' (measurableSet_Om γ w n)).2 (Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs]
  exact hK x hx

lemma prod_inv_bounds {γ w : ℝ} (hγ : 0 < γ) {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ Om γ w n) :
    0 ≤ ∏ i, (x i)⁻¹ ∧ ∏ i, (x i)⁻¹ ≤ γ⁻¹ ^ n := by
  have hi : ∀ i, 0 < x i := fun i => lt_of_lt_of_le hγ (hx.1 i)
  refine ⟨Finset.prod_nonneg fun i _ => (inv_pos.2 (hi i)).le, ?_⟩
  calc ∏ i, (x i)⁻¹ ≤ ∏ _i : Fin n, γ⁻¹ :=
        Finset.prod_le_prod (fun i _ => (inv_pos.2 (hi i)).le) fun i _ => inv_anti₀ hγ (hx.1 i)
    _ = γ⁻¹ ^ n := by simp

lemma gap_bounds {γ w w' : ℝ} (hγ : 0 < γ) (hw : w ≤ w') {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ Om γ w n) :
    0 ≤ γ⁻¹ - (w' - ∑ i, x i)⁻¹ ∧ γ⁻¹ - (w' - ∑ i, x i)⁻¹ ≤ γ⁻¹ ∧
      γ⁻¹ - (w - ∑ i, x i)⁻¹ ≤ γ⁻¹ - (w' - ∑ i, x i)⁻¹ := by
  have h1 : γ ≤ w - ∑ i, x i := by linarith [hx.2]
  have h2 : γ ≤ w' - ∑ i, x i := by linarith
  refine ⟨sub_nonneg.2 (inv_anti₀ hγ h2), ?_, ?_⟩
  · have : 0 ≤ (w' - ∑ i, x i)⁻¹ := inv_nonneg.2 (by linarith)
    linarith
  · have := inv_anti₀ (lt_of_lt_of_le hγ h1) (by linarith : w - ∑ i, x i ≤ w' - ∑ i, x i)
    linarith

lemma measurable_prod_inv (n : ℕ) : Measurable (fun x : Fin n → ℝ => ∏ i, (x i)⁻¹) :=
  Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).inv

lemma measurable_gap (γ w : ℝ) (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => (γ⁻¹ - (w - ∑ i, x i)⁻¹)) :=
  measurable_const.sub
    ((measurable_const.sub (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)).inv)

/-- The increasing part of the simplex integral. -/
noncomputable def P (γ w : ℝ) (n : ℕ) : ℝ := ∫ x in Om γ w n, γ⁻¹ * ∏ i, (x i)⁻¹

/-- The subtracted part of the simplex integral. -/
noncomputable def Q (γ w : ℝ) (n : ℕ) : ℝ :=
  ∫ x in Om γ w n, (γ⁻¹ - (w - ∑ i, x i)⁻¹) * ∏ i, (x i)⁻¹

lemma integrableOn_P {γ : ℝ} (hγ : 0 < γ) (w : ℝ) (n : ℕ) :
    IntegrableOn (fun x : Fin n → ℝ => γ⁻¹ * ∏ i, (x i)⁻¹) (Om γ w n) := by
  refine integrableOn_Om hγ (measurable_const.mul (measurable_prod_inv n)) (γ⁻¹ * γ⁻¹ ^ n)
    fun x hx => ?_
  obtain ⟨h0, h1⟩ := prod_inv_bounds hγ hx
  rw [abs_of_nonneg (mul_nonneg (inv_pos.2 hγ).le h0)]
  exact mul_le_mul_of_nonneg_left h1 (inv_pos.2 hγ).le

lemma integrableOn_Q {γ : ℝ} (hγ : 0 < γ) {w w' : ℝ} (hw : w ≤ w') (n : ℕ) :
    IntegrableOn (fun x : Fin n → ℝ => (γ⁻¹ - (w' - ∑ i, x i)⁻¹) * ∏ i, (x i)⁻¹)
      (Om γ w n) := by
  refine integrableOn_Om hγ ((measurable_gap γ w' n).mul (measurable_prod_inv n))
    (γ⁻¹ * γ⁻¹ ^ n) fun x hx => ?_
  obtain ⟨h0, h1⟩ := prod_inv_bounds hγ hx
  obtain ⟨g0, g1, -⟩ := gap_bounds hγ hw hx
  rw [abs_of_nonneg (mul_nonneg g0 h0)]
  exact mul_le_mul g1 h1 h0 (inv_pos.2 hγ).le

lemma P_nonneg {γ : ℝ} (hγ : 0 < γ) (w : ℝ) (n : ℕ) : 0 ≤ P γ w n :=
  setIntegral_nonneg (measurableSet_Om γ w n) fun _ hx =>
    mul_nonneg (inv_pos.2 hγ).le (prod_inv_bounds hγ hx).1

lemma Q_nonneg {γ : ℝ} (hγ : 0 < γ) (w : ℝ) (n : ℕ) : 0 ≤ Q γ w n :=
  setIntegral_nonneg (measurableSet_Om γ w n) fun _ hx =>
    mul_nonneg (gap_bounds hγ le_rfl hx).1 (prod_inv_bounds hγ hx).1

lemma P_mono {γ : ℝ} (hγ : 0 < γ) (n : ℕ) : Monotone (fun w => P γ w n) := by
  intro w w' h
  refine setIntegral_mono_set (integrableOn_P hγ w' n) ?_
    (Eventually.of_forall (Om_mono γ h n))
  refine (ae_restrict_iff' (measurableSet_Om γ w' n)).2 (Eventually.of_forall fun x hx => ?_)
  exact mul_nonneg (inv_pos.2 hγ).le (prod_inv_bounds hγ hx).1

lemma Q_mono {γ : ℝ} (hγ : 0 < γ) (n : ℕ) : Monotone (fun w => Q γ w n) := by
  intro w w' h
  calc Q γ w n
      ≤ ∫ x in Om γ w n, (γ⁻¹ - (w' - ∑ i, x i)⁻¹) * ∏ i, (x i)⁻¹ := by
        refine setIntegral_mono_on (integrableOn_Q hγ le_rfl n) (integrableOn_Q hγ h n)
          (measurableSet_Om γ w n) fun x hx => ?_
        exact mul_le_mul_of_nonneg_right (gap_bounds hγ h hx).2.2 (prod_inv_bounds hγ hx).1
    _ ≤ Q γ w' n := by
        refine setIntegral_mono_set (integrableOn_Q hγ le_rfl n) ?_
          (Eventually.of_forall (Om_mono γ h n))
        refine (ae_restrict_iff' (measurableSet_Om γ w' n)).2
          (Eventually.of_forall fun x hx => ?_)
        exact mul_nonneg (gap_bounds hγ le_rfl hx).1 (prod_inv_bounds hγ hx).1

/-- The simplex integral of `D_{γ, n+1}` (times `(n+1)!`). -/
noncomputable def I (γ w : ℝ) (n : ℕ) : ℝ :=
  ∫ x in Om γ w n, (w - ∑ i, x i)⁻¹ * ∏ i, (x i)⁻¹

lemma I_eq_P_sub_Q {γ : ℝ} (hγ : 0 < γ) (w : ℝ) (n : ℕ) : I γ w n = P γ w n - Q γ w n := by
  unfold I P Q
  rw [← integral_sub (integrableOn_P hγ w n) (integrableOn_Q hγ le_rfl n)]
  congr 1
  funext x
  ring

lemma I_zero (γ w : ℝ) (h : γ ≤ w) : I γ w 0 = w⁻¹ := by
  have hO : Om γ w 0 = univ := by
    ext x; simp [Om]; linarith
  simp [I, hO, Measure.real, volume_pi]

lemma I_eq_zero (γ w : ℝ) (_hγ : 0 < γ) (n : ℕ) (h : w < (n + 1) * γ) : I γ w n = 0 := by
  have hO : Om γ w n = ∅ := by
    ext x
    simp only [Om, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
    intro hx
    have : ∑ _i : Fin n, γ ≤ ∑ i, x i := Finset.sum_le_sum fun i _ => hx i
    simp at this
    nlinarith
  simp [I, hO]

lemma term_succ (γ w : ℝ) (hγ : γ ≤ w) (n : ℕ) :
    roughDensityTerm γ w (n + 1) = I γ w n / ((n + 1).factorial : ℝ) := by
  rcases n with _ | n
  · simp [roughDensityTerm, I_zero γ w hγ]
  · simp only [roughDensityTerm, I, Om]
    ring

lemma roughDensity_eq_sum (γ w : ℝ) (hγ : 0 < γ) (hw : γ ≤ w) (N : ℕ)
    (hN : w < (N + 1) * γ) :
    roughDensity γ w = ∑ n ∈ Finset.range N, I γ w n / ((n + 1).factorial : ℝ) := by
  unfold roughDensity
  rw [tsum_eq_sum (s := Finset.range (N + 1))]
  · rw [Finset.sum_range_succ']
    simp only [roughDensityTerm, add_zero]
    exact Finset.sum_congr rfl fun n _ => term_succ γ w hw n
  · intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    rw [term_succ γ w hw n, I_eq_zero γ w hγ n, zero_div]
    have : (N : ℝ) + 1 ≤ n + 1 := by exact_mod_cast (by omega : N + 1 ≤ n + 1)
    nlinarith

/-- The nondecreasing part `D⁺` of `D_γ`. -/
noncomputable def Dp (γ : ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, P γ w n / ((n + 1).factorial : ℝ)

/-- The nondecreasing part `D⁻` subtracted from `D⁺`. -/
noncomputable def Dm (γ : ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, Q γ w n / ((n + 1).factorial : ℝ)

lemma roughDensity_eq_Dp_sub_Dm {γ w : ℝ} (hγ : 0 < γ) (hw : γ ≤ w) {N : ℕ}
    (hN : w < (N + 1) * γ) : roughDensity γ w = Dp γ N w - Dm γ N w := by
  rw [roughDensity_eq_sum γ w hγ hw N hN, Dp, Dm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [I_eq_P_sub_Q hγ, sub_div]

lemma Dp_mono {γ : ℝ} (hγ : 0 < γ) (N : ℕ) : Monotone (Dp γ N) := fun _ _ h =>
  Finset.sum_le_sum fun n _ => div_le_div_of_nonneg_right (P_mono hγ n h) (by positivity)

lemma Dm_mono {γ : ℝ} (hγ : 0 < γ) (N : ℕ) : Monotone (Dm γ N) := fun _ _ h =>
  Finset.sum_le_sum fun n _ => div_le_div_of_nonneg_right (Q_mono hγ n h) (by positivity)

lemma Dp_nonneg {γ : ℝ} (hγ : 0 < γ) (N : ℕ) (w : ℝ) : 0 ≤ Dp γ N w :=
  Finset.sum_nonneg fun n _ => div_nonneg (P_nonneg hγ w n) (by positivity)

lemma Dm_nonneg {γ : ℝ} (hγ : 0 < γ) (N : ℕ) (w : ℝ) : 0 ≤ Dm γ N w :=
  Finset.sum_nonneg fun n _ => div_nonneg (Q_nonneg hγ w n) (by positivity)

end ArtinPrimitiveRoots.A106R
end

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

lemma natCast_cpow_I_mul (j : ℕ) (u : ℝ) (hj : 0 < j) :
    (j : ℂ) ^ (Complex.I * u) = Complex.exp (Complex.I * ((u * Real.log j : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hj.ne'), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg j)]
  push_cast; ring_nf

lemma norm_natCast_cpow_I_mul_le (j : ℕ) (u : ℝ) : ‖(j : ℂ) ^ (Complex.I * u)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [Nat.cast_zero]
    by_cases hu : Complex.I * (u : ℂ) = 0
    · rw [hu, Complex.cpow_zero, norm_one]
    · rw [Complex.zero_cpow hu, norm_zero]; exact zero_le_one
  · rw [Complex.norm_natCast_cpow_of_pos hj]
    simp

lemma norm_exp_sub_exp_le (θ φ : ℝ) :
    ‖Complex.exp (Complex.I * θ) - Complex.exp (Complex.I * φ)‖ ≤ |θ - φ| := by
  have : Complex.exp (Complex.I * θ) - Complex.exp (Complex.I * φ) =
      Complex.exp (Complex.I * φ) * (Complex.exp (Complex.I * ((θ - φ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]; push_cast; ring_nf
  rw [this, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, ← Real.norm_eq_abs]
  exact norm_exp_I_mul_ofReal_sub_one_le

lemma norm_cpow_succ_sub_le (i : ℕ) (u : ℝ) :
    ‖((i + 1 : ℕ) : ℂ) ^ (Complex.I * u) - (i : ℂ) ^ (Complex.I * u)‖ ≤
      (if i = 0 then 2 else 0) + |u| * (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ)) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [if_pos rfl]
    simp only [zero_add, Nat.cast_one, Real.log_one, Nat.cast_zero, Real.log_zero,
      sub_zero, mul_zero, add_zero]
    calc _ ≤ ‖(1 : ℂ) ^ (Complex.I * u)‖ + ‖(0 : ℂ) ^ (Complex.I * u)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (by simp)
          (by simpa using norm_natCast_cpow_I_mul_le 0 u)
      _ = 2 := by norm_num
  · rw [if_neg hi.ne', zero_add, natCast_cpow_I_mul _ _ (Nat.succ_pos i),
      natCast_cpow_I_mul _ _ hi]
    refine (norm_exp_sub_exp_le _ _).trans (le_of_eq ?_)
    have hle : Real.log (i : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hi) (by push_cast; linarith)
    rw [← mul_sub, abs_mul, abs_of_nonneg (sub_nonneg.2 hle)]

/-- Discrete Abel summation against `j^{iu}`: if all partial sums are at most `δ`, the twisted
sum is at most `δ (3 + |u| log n)`. -/
theorem abel_cpow (a : ℕ → ℂ) (n : ℕ) (u δ : ℝ)
    (hA : ∀ k ≤ n, ‖∑ j ∈ Finset.range k, a j‖ ≤ δ) :
    ‖∑ j ∈ Finset.range n, a j * (j : ℂ) ^ (Complex.I * u)‖ ≤ δ * (3 + |u| * Real.log n) := by
  have hδ : 0 ≤ δ := by simpa using hA 0 (Nat.zero_le _)
  set f : ℕ → ℂ := fun j => (j : ℂ) ^ (Complex.I * u) with hf
  have hsum : ∑ j ∈ Finset.range n, a j * f j = ∑ j ∈ Finset.range n, f j • a j :=
    Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul, mul_comm]
  rw [show (∑ j ∈ Finset.range n, a j * (j : ℂ) ^ (Complex.I * u)) =
      ∑ j ∈ Finset.range n, a j * f j from rfl, hsum, Finset.sum_range_by_parts]
  have h1 : ‖f (n - 1) • ∑ i ∈ Finset.range n, a i‖ ≤ δ := by
    rw [norm_smul]
    calc ‖f (n - 1)‖ * ‖∑ i ∈ Finset.range n, a i‖ ≤ 1 * δ :=
          mul_le_mul (norm_natCast_cpow_I_mul_le _ _) (hA n le_rfl) (norm_nonneg _) zero_le_one
      _ = δ := one_mul δ
  have h2 : ‖∑ i ∈ Finset.range (n - 1), (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), a j‖ ≤
      δ * (2 + |u| * Real.log n) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Finset.range (n - 1),
        ‖(f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), a j‖ ≤
          δ * ((if i = 0 then 2 else 0) +
            |u| * (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ))) := by
      intro i hi
      rw [norm_smul, mul_comm]
      refine mul_le_mul (hA _ ?_) ?_ (norm_nonneg _) hδ
      · simp only [Finset.mem_range] at hi; omega
      · have := norm_cpow_succ_sub_le i u
        simpa [hf] using this
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
      Finset.sum_range_sub (fun i => Real.log (i : ℝ))]
    refine mul_le_mul_of_nonneg_left ?_ hδ
    have hlog : Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log n := by
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n <;> simp
      · exact Real.log_le_log (by exact_mod_cast (by omega : 0 < n - 1))
          (by exact_mod_cast Nat.sub_le n 1)
    have hu := abs_nonneg u
    have : (if (0 : ℕ) ∈ Finset.range (n - 1) then (2 : ℝ) else 0) ≤ 2 := by
      split_ifs <;> norm_num
    simp only [Nat.cast_zero, Real.log_zero, sub_zero]
    nlinarith
  calc ‖f (n - 1) • ∑ i ∈ Finset.range n, a i -
        ∑ i ∈ Finset.range (n - 1), (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), a j‖
      ≤ δ + δ * (2 + |u| * Real.log n) := (norm_sub_le _ _).trans (add_le_add h1 h2)
    _ = δ * (3 + |u| * Real.log n) := by ring

end ArtinPrimitiveRoots.A106R
end

section
/-!
# (10.6) for the rough-factor coefficient (10.13), from the cuts (10.15), (10.17), the
# high-frequency prime-product bound and (10.19)

Write `u = t + v`. At low frequencies `|t| ≤ L^{B₂}` the partial sums of `χ(R_γ - B_γ)` over
every initial segment of the interval are `O(M L^{-A₁})`: (10.15) for `R_γ`, and (10.17)
summed against the monotone pieces of `D_γ(log y/L)/(L V(W))` (`layer_cake_sum`) for `B_γ`; the
two main terms are both `1_{χ=1} (1/L) ∫ D_γ(log y/L) dy` and cancel. Abel summation against
`m^{iu}` (`abel_cpow`) costs `O(1 + |u| L)`. At high frequencies the `R_γ` part is
`rough_prime_product_high_frequency`, and the `B_γ` part is (10.19) summed against the monotone
pieces of `w D_γ(w)`, `w = log m/L`.
-/

namespace ArtinPrimitiveRoots.A106R

open Real MeasureTheory Set Filter Topology

/-! ## The weights -/

lemma weight_low {D : ℝ → ℝ} (hD : Monotone D) (hD0 : ∀ w, 0 ≤ D w) {M L V wmax : ℝ}
    (hM : 0 < M) (hL : 0 < L) (hLV : 0 < L * V)
    (hwmax : ∀ y ∈ Icc M (2 * M), log y / L ≤ wmax) :
    MonotoneOn (fun y => D (log y / L) / (L * V)) (Icc M (2 * M)) ∧
    (∀ y ∈ Icc M (2 * M), 0 ≤ D (log y / L) / (L * V)) ∧
    (∀ y ∈ Icc M (2 * M), D (log y / L) / (L * V) ≤ D wmax / (L * V)) ∧
    0 ≤ D wmax / (L * V) := by
  refine ⟨fun y₁ hy₁ y₂ _ h => ?_, fun y _ => div_nonneg (hD0 _) hLV.le,
    fun y hy => div_le_div_of_nonneg_right (hD (hwmax y hy)) hLV.le, div_nonneg (hD0 _) hLV.le⟩
  exact div_le_div_of_nonneg_right
    (hD (div_le_div_of_nonneg_right (log_le_log (hM.trans_le hy₁.1) h) hL.le)) hLV.le

lemma weight_high {D : ℝ → ℝ} (hD : Monotone D) (hD0 : ∀ w, 0 ≤ D w) {M L wmax : ℝ}
    (hM : 1 ≤ M) (hL : 0 < L) (hwmax : ∀ y ∈ Icc M (2 * M), log y / L ≤ wmax) :
    MonotoneOn (fun y => log y / L * D (log y / L)) (Icc M (2 * M)) ∧
    (∀ y ∈ Icc M (2 * M), 0 ≤ log y / L * D (log y / L)) ∧
    (∀ y ∈ Icc M (2 * M), log y / L * D (log y / L) ≤ wmax * D wmax) ∧
    0 ≤ wmax * D wmax := by
  have hw0 : ∀ y ∈ Icc M (2 * M), 0 ≤ log y / L := fun y hy =>
    div_nonneg (log_nonneg (hM.trans hy.1)) hL.le
  have hMmem : M ∈ Icc M (2 * M) := ⟨le_rfl, by linarith⟩
  have hwmax0 : 0 ≤ wmax := (hw0 M hMmem).trans (hwmax M hMmem)
  refine ⟨fun y₁ hy₁ y₂ _ h => ?_, fun y hy => mul_nonneg (hw0 y hy) (hD0 _),
    fun y hy => mul_le_mul (hwmax y hy) (hD (hwmax y hy)) (hD0 _) hwmax0,
    mul_nonneg hwmax0 (hD0 _)⟩
  have hw : log y₁ / L ≤ log y₂ / L :=
    div_le_div_of_nonneg_right (log_le_log (by linarith [hy₁.1]) h) hL.le
  exact mul_le_mul hw (hD hw) (hD0 _) ((hw0 y₁ hy₁).trans hw)

/-! ## Low frequencies -/

open Classical in
/-- The partial sums of `χ (R_γ - B_γ)` over a subinterval: the main terms of (10.15) and of
(10.17) summed against `D_γ(log y/L)/(L V)` cancel. -/
lemma low_partial {γ : ℝ} (hγ : 0 < γ) (N : ℕ) {x M V W wmax : ℝ} (hL : 0 < log x)
    (hV : 0 < V) (hM : 0 < M)
    (hrange : ∀ y ∈ Icc M (2 * M), γ ≤ log y / log x ∧ log y / log x < (N + 1) * γ)
    (hwmax : ∀ y ∈ Icc M (2 * M), log y / log x ≤ wmax)
    (S : Finset ℕ) (χc : ℕ → ℂ) (b : Prop) [Decidable b] (ε₁ ε₂ : ℝ)
    (h15 : ∀ J' : Set ℝ, J'.OrdConnected → J' ⊆ Icc M (2 * M) →
      ‖(∑ m ∈ S, if (m : ℝ) ∈ J' ∧ IsRough (x ^ γ) m then χc m else 0) -
        (if b then (((1 / log x) * ∫ y in J', roughDensity γ (log y / log x) : ℝ) : ℂ)
          else 0)‖ ≤ ε₁)
    (h17 : ∀ J' : Set ℝ, J'.OrdConnected → J' ⊆ Icc M (2 * M) →
      ‖(∑ m ∈ S, if (m : ℝ) ∈ J' ∧ IsRough W m then χc m else 0) -
        (if b then ((V * (volume J').toReal : ℝ) : ℂ) else 0)‖ ≤ ε₂)
    (J' : Set ℝ) (hJ' : J'.OrdConnected) (hJ'sub : J' ⊆ Icc M (2 * M)) :
    ‖∑ m ∈ S, if (m : ℝ) ∈ J' then
        χc m * ((if IsRough (x ^ γ) m then 1 else 0) -
          ((roughDensity γ (log m / log x) / (log x * V) : ℝ) : ℂ) *
            (if IsRough W m then 1 else 0)) else 0‖ ≤
      ε₁ + (Dp γ N wmax / (log x * V) + Dm γ N wmax / (log x * V)) * ε₂ := by
  have hLV : 0 < log x * V := mul_pos hL hV
  obtain ⟨hpmono, hp0, hpΨ, hpΨ0⟩ :=
    weight_low (Dp_mono hγ N) (Dp_nonneg hγ N) hM hL hLV hwmax
  obtain ⟨hmmono, hm0, hmΨ, hmΨ0⟩ :=
    weight_low (Dm_mono hγ N) (Dm_nonneg hγ N) hM hL hLV hwmax
  set ψp : ℝ → ℝ := fun y => Dp γ N (log y / log x) / (log x * V) with hψp
  set ψm : ℝ → ℝ := fun y => Dm γ N (log y / log x) / (log x * V) with hψm
  set c : ℕ → ℂ := fun m => if IsRough W m then χc m else 0 with hc
  set κ : ℂ := if b then (V : ℂ) else 0 with hκ
  have h17' : ∀ J'' : Set ℝ, J''.OrdConnected → J'' ⊆ J' →
      ‖(∑ m ∈ S, if (m : ℝ) ∈ J'' then c m else 0) - κ * ((volume J'').toReal : ℂ)‖ ≤ ε₂ := by
    intro J'' hJ'' hsub
    convert h17 J'' hJ'' (hsub.trans hJ'sub) using 3
    · refine Finset.sum_congr rfl fun m _ => ?_
      simp only [hc, ite_and]
    · simp only [hκ]
      split_ifs <;> push_cast <;> ring
  have hPp := layer_cake_sum S hJ' hJ'sub hpmono hpΨ0 (fun y hy => hp0 y (hJ'sub hy))
    (fun y hy => hpΨ y (hJ'sub hy)) c κ ε₂ h17'
  have hPm := layer_cake_sum S hJ' hJ'sub hmmono hmΨ0 (fun y hy => hm0 y (hJ'sub hy))
    (fun y hy => hmΨ y (hJ'sub hy)) c κ ε₂ h17'
  have hR := h15 J' hJ' hJ'sub
  have hint_p : IntegrableOn ψp J' :=
    (hpmono.integrableOn_isCompact isCompact_Icc).mono_set hJ'sub
  have hint_m : IntegrableOn ψm J' :=
    (hmmono.integrableOn_isCompact isCompact_Icc).mono_set hJ'sub
  have hmain : κ * ((∫ y in J', ψp y : ℝ) : ℂ) - κ * ((∫ y in J', ψm y : ℝ) : ℂ) =
      (if b then (((1 / log x) * ∫ y in J', roughDensity γ (log y / log x) : ℝ) : ℂ)
        else 0) := by
    have hdiff : (∫ y in J', ψp y) - (∫ y in J', ψm y) =
        (∫ y in J', roughDensity γ (log y / log x)) / (log x * V) := by
      rw [← integral_sub hint_p hint_m, ← integral_div]
      refine setIntegral_congr_fun hJ'.measurableSet fun y hy => ?_
      obtain ⟨h1, h2⟩ := hrange y (hJ'sub hy)
      simp only [hψp, hψm]
      rw [roughDensity_eq_Dp_sub_Dm hγ h1 h2, sub_div]
    rw [← mul_sub, ← Complex.ofReal_sub, hdiff, hκ]
    split_ifs
    · have hVC : ((V : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hV.ne'
      have hLC : ((log x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      push_cast
      field_simp
    · simp
  have hsplit : (∑ m ∈ S, if (m : ℝ) ∈ J' then
        χc m * ((if IsRough (x ^ γ) m then 1 else 0) -
          ((roughDensity γ (log m / log x) / (log x * V) : ℝ) : ℂ) *
            (if IsRough W m then 1 else 0)) else 0) =
      (∑ m ∈ S, if (m : ℝ) ∈ J' ∧ IsRough (x ^ γ) m then χc m else 0) -
        ((∑ m ∈ S, if (m : ℝ) ∈ J' then c m * (ψp m : ℂ) else 0) -
          (∑ m ∈ S, if (m : ℝ) ∈ J' then c m * (ψm m : ℂ) else 0)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : (m : ℝ) ∈ J'
    · obtain ⟨h1, h2⟩ := hrange _ (hJ'sub hm)
      have hρ := roughDensity_eq_Dp_sub_Dm hγ h1 h2 (N := N)
      simp only [hm, true_and, if_true, hc, hψp, hψm, hρ]
      split_ifs <;> push_cast <;> ring
    · simp [hm]
  set TR : ℂ := if b then (((1 / log x) * ∫ y in J', roughDensity γ (log y / log x) : ℝ) : ℂ)
    else 0 with hTR
  rw [hsplit]
  set SR := ∑ m ∈ S, if (m : ℝ) ∈ J' ∧ IsRough (x ^ γ) m then χc m else 0
  set Sp := ∑ m ∈ S, if (m : ℝ) ∈ J' then c m * (ψp m : ℂ) else 0
  set Sm := ∑ m ∈ S, if (m : ℝ) ∈ J' then c m * (ψm m : ℂ) else 0
  set Ip : ℂ := κ * ((∫ y in J', ψp y : ℝ) : ℂ)
  set Im : ℂ := κ * ((∫ y in J', ψm y : ℝ) : ℂ)
  have heq : SR - (Sp - Sm) = (SR - TR) - ((Sp - Ip) - (Sm - Im)) := by
    rw [← hmain]; ring
  rw [heq]
  calc ‖(SR - TR) - ((Sp - Ip) - (Sm - Im))‖
      ≤ ‖SR - TR‖ + (‖Sp - Ip‖ + ‖Sm - Im‖) :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    _ ≤ ε₁ + (Dp γ N wmax / (log x * V) * ε₂ + Dm γ N wmax / (log x * V) * ε₂) :=
        add_le_add hR (add_le_add hPp hPm)
    _ = _ := by ring

open Classical in
/-- The low-frequency bound: Abel summation of `low_partial` against `m^{iu}`. -/
lemma low_freq {γ : ℝ} (hγ : 0 < γ) (N : ℕ) {x M V W wmax : ℝ} (hL : 0 < log x)
    (hV : 0 < V) (hM : 0 < M)
    (hrange : ∀ y ∈ Icc M (2 * M), γ ≤ log y / log x ∧ log y / log x < (N + 1) * γ)
    (hwmax : ∀ y ∈ Icc M (2 * M), log y / log x ≤ wmax)
    (χc : ℕ → ℂ) (b : Prop) [Decidable b] (ε₁ ε₂ : ℝ)
    (h15 : ∀ J' : Set ℝ, J'.OrdConnected → J' ⊆ Icc M (2 * M) →
      ‖(∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
          if (m : ℝ) ∈ J' ∧ IsRough (x ^ γ) m then χc m else 0) -
        (if b then (((1 / log x) * ∫ y in J', roughDensity γ (log y / log x) : ℝ) : ℂ)
          else 0)‖ ≤ ε₁)
    (h17 : ∀ J' : Set ℝ, J'.OrdConnected → J' ⊆ Icc M (2 * M) →
      ‖(∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1), if (m : ℝ) ∈ J' ∧ IsRough W m then χc m else 0) -
        (if b then ((V * (volume J').toReal : ℝ) : ℂ) else 0)‖ ≤ ε₂)
    (J : Set ℝ) (hJ : J.OrdConnected) (hJsub : J ⊆ Icc M (2 * M)) (u : ℝ) :
    ‖∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1), (if (m : ℝ) ∈ J then
        χc m * ((if IsRough (x ^ γ) m then 1 else 0) -
          ((roughDensity γ (log m / log x) / (log x * V) : ℝ) : ℂ) *
            (if IsRough W m then 1 else 0)) else 0) * (m : ℂ) ^ (Complex.I * u)‖ ≤
      (ε₁ + (Dp γ N wmax / (log x * V) + Dm γ N wmax / (log x * V)) * ε₂) *
        (3 + |u| * log ((⌊2 * M⌋₊ + 1 : ℕ) : ℝ)) := by
  refine abel_cpow _ _ u _ fun k hk => ?_
  have hJk : (J ∩ Iio (k : ℝ)).OrdConnected := hJ.inter ordConnected_Iio
  have h := low_partial hγ N hL hV hM hrange hwmax _ χc b ε₁ ε₂ h15 h17 (J ∩ Iio (k : ℝ)) hJk
    (inter_subset_left.trans hJsub)
  convert h using 2
  have hfilt : (Finset.range (⌊2 * M⌋₊ + 1)).filter (· < k) = Finset.range k := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [← hfilt, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [mem_inter_iff, mem_Iio, Nat.cast_lt]
  by_cases h1 : (m : ℝ) ∈ J <;> by_cases h2 : m < k <;> simp [h1, h2]

/-! ## High frequencies -/

open Classical in
/-- The proxy part at high frequencies: (10.19) summed against `w D_γ(w)`. -/
lemma high_proxy {γ : ℝ} (hγ : 0 < γ) (N : ℕ) {x M V W wmax : ℝ} (hL : 0 < log x)
    (hV : 0 < V) (hM : 1 < M)
    (hrange : ∀ y ∈ Icc M (2 * M), γ ≤ log y / log x ∧ log y / log x < (N + 1) * γ)
    (hwmax : ∀ y ∈ Icc M (2 * M), log y / log x ≤ wmax)
    (S : Finset ℕ) (χc : ℕ → ℂ) (u ε : ℝ) (J : Set ℝ) (hJ : J.OrdConnected)
    (hJsub : J ⊆ Icc M (2 * M))
    (h19 : ∀ J' : Set ℝ, J'.OrdConnected → J' ⊆ J →
      ‖∑ m ∈ S, if (m : ℝ) ∈ J' ∧ IsRough W m then
        χc m * (m : ℂ) ^ (Complex.I * u) / ((log m : ℝ) : ℂ) else 0‖ ≤ ε) :
    ‖∑ m ∈ S, if (m : ℝ) ∈ J then
        (if IsRough W m then χc m * (m : ℂ) ^ (Complex.I * u) else 0) *
          ((roughDensity γ (log m / log x) / (log x * V) : ℝ) : ℂ) else 0‖ ≤
      (wmax * Dp γ N wmax + wmax * Dm γ N wmax) / V * ε := by
  obtain ⟨hpmono, hp0, hpΩ, hpΩ0⟩ :=
    weight_high (Dp_mono hγ N) (Dp_nonneg hγ N) hM.le hL hwmax
  obtain ⟨hmmono, hm0, hmΩ, hmΩ0⟩ :=
    weight_high (Dm_mono hγ N) (Dm_nonneg hγ N) hM.le hL hwmax
  set ωp : ℝ → ℝ := fun y => log y / log x * Dp γ N (log y / log x) with hωp
  set ωm : ℝ → ℝ := fun y => log y / log x * Dm γ N (log y / log x) with hωm
  set c : ℕ → ℂ := fun m => if IsRough W m then
    χc m * (m : ℂ) ^ (Complex.I * u) / ((log m : ℝ) : ℂ) else 0 with hc
  have h19' : ∀ J'' : Set ℝ, J''.OrdConnected → J'' ⊆ J →
      ‖(∑ m ∈ S, if (m : ℝ) ∈ J'' then c m else 0) - 0 * ((volume J'').toReal : ℂ)‖ ≤ ε := by
    intro J'' hJ'' hsub
    rw [zero_mul, sub_zero]
    convert h19 J'' hJ'' hsub using 2
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hc, ite_and]
  have hPp := layer_cake_sum S hJ hJsub hpmono hpΩ0 (fun y hy => hp0 y (hJsub hy))
    (fun y hy => hpΩ y (hJsub hy)) c 0 ε h19'
  have hPm := layer_cake_sum S hJ hJsub hmmono hmΩ0 (fun y hy => hm0 y (hJsub hy))
    (fun y hy => hmΩ y (hJsub hy)) c 0 ε h19'
  simp only [zero_mul, sub_zero] at hPp hPm
  have hsum : (∑ m ∈ S, if (m : ℝ) ∈ J then
        (if IsRough W m then χc m * (m : ℂ) ^ (Complex.I * u) else 0) *
          ((roughDensity γ (log m / log x) / (log x * V) : ℝ) : ℂ) else 0) =
      ((1 / V : ℝ) : ℂ) * ((∑ m ∈ S, if (m : ℝ) ∈ J then c m * (ωp m : ℂ) else 0) -
        (∑ m ∈ S, if (m : ℝ) ∈ J then c m * (ωm m : ℂ) else 0)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : (m : ℝ) ∈ J
    · have hmy := hJsub hm
      obtain ⟨h1, h2⟩ := hrange _ hmy
      have hρ := roughDensity_eq_Dp_sub_Dm hγ h1 h2 (N := N)
      have hlog : log (m : ℝ) ≠ 0 := (log_pos (by linarith [hmy.1])).ne'
      have hlogC : ((log (m : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
      have hLC : ((log x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      have hVC : ((V : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hV.ne'
      have hlogC' : Complex.log (m : ℂ) ≠ 0 := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg m)]; exact hlogC
      simp only [hm, if_true, hc, hωp, hωm, hρ]
      split_ifs
      · push_cast
        field_simp
      · simp
    · simp [hm]
  rw [hsum, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 1 / V * ‖(∑ m ∈ S, if (m : ℝ) ∈ J then c m * (ωp m : ℂ) else 0) -
        (∑ m ∈ S, if (m : ℝ) ∈ J then c m * (ωm m : ℂ) else 0)‖
      ≤ 1 / V * (wmax * Dp γ N wmax * ε + wmax * Dm γ N wmax * ε) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hPp hPm))
          (by positivity)
    _ = _ := by ring

/-! ## Eventual inequalities -/

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

lemma ev_poly (B C : ℝ) : ∀ᶠ x in atTop, x * log x ^ B + log x ^ C < x ^ 2 := by
  have h1 := (isLittleO_log_rpow_rpow_atTop B one_pos).bound (by norm_num : (0 : ℝ) < 1 / 4)
  have h2 := (isLittleO_log_rpow_rpow_atTop C one_pos).bound (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [h1, h2, eventually_ge_atTop 1] with x h1 h2 hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, rpow_one, abs_of_pos (show (0 : ℝ) < x by linarith)]
    at h1 h2
  have hB := (le_abs_self (log x ^ B)).trans h1
  have hC := (le_abs_self (log x ^ C)).trans h2
  have : x * log x ^ B ≤ x * (1 / 4 * x) := mul_le_mul_of_nonneg_left hB (by linarith)
  nlinarith

lemma ev_E1 (C₀ c₀ A : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ x in atTop, log x ^ C₀ * x ^ (-c₀) ≤ log x ^ (-A) := by
  have h := (isLittleO_log_rpow_rpow_atTop (C₀ + A) hc₀).bound one_pos
  filter_upwards [h, eventually_gt_atTop (exp 1)] with x h hx
  have hx0 : 0 < x := (exp_pos 1).trans hx
  have hL : 0 < log x := by
    have : 1 < log x := by rw [← log_exp 1]; exact log_lt_log (exp_pos 1) hx
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_pos (rpow_pos_of_pos hL _),
    abs_of_pos (rpow_pos_of_pos hx0 _)] at h
  have hsplit : log x ^ C₀ = log x ^ (C₀ + A) * log x ^ (-A) := by
    rw [← rpow_add hL]; ring_nf
  have hxc : x ^ (-c₀) = (x ^ c₀)⁻¹ := rpow_neg hx0.le _
  have hxpos : 0 < x ^ c₀ := rpow_pos_of_pos hx0 _
  rw [hsplit, hxc]
  calc log x ^ (C₀ + A) * log x ^ (-A) * (x ^ c₀)⁻¹
      ≤ x ^ c₀ * log x ^ (-A) * (x ^ c₀)⁻¹ := by
        gcongr
    _ = log x ^ (-A) := by field_simp

lemma ev_E2 (C₀ C₃ A : ℝ) (hpos : 0 < C₀ + A) :
    ∀ᶠ x in atTop, log x ^ C₀ * exp (-(log x / log (log x) ^ C₃)) ≤ log x ^ (-A) := by
  have h := (isLittleO_log_rpow_rpow_atTop (C₃ + 1) one_pos).bound (inv_pos.2 hpos)
  have hL : ∀ᶠ L in atTop, log L ^ (C₃ + 1) ≤ (C₀ + A)⁻¹ * L ∧ exp 1 < L := by
    filter_upwards [h, eventually_gt_atTop (exp 1)] with L h hL
    have hL0 : 0 < L := (exp_pos 1).trans hL
    have hl : 1 < log L := by rw [← log_exp 1]; exact log_lt_log (exp_pos 1) hL
    rw [Real.norm_eq_abs, Real.norm_eq_abs, rpow_one, abs_of_pos hL0,
      abs_of_pos (rpow_pos_of_pos (by linarith) _)] at h
    exact ⟨h, hL⟩
  filter_upwards [tendsto_log_atTop.eventually hL] with x hx
  obtain ⟨h1, h2⟩ := hx
  set L := log x
  have hL0 : 0 < L := (exp_pos 1).trans h2
  have hl : 1 < log L := by rw [← log_exp 1]; exact log_lt_log (exp_pos 1) h2
  have hl0 : 0 < log L := by linarith
  have hlC : 0 < log L ^ C₃ := rpow_pos_of_pos hl0 _
  rw [rpow_add_one hl0.ne'] at h1
  have hkey : (C₀ + A) * log L ≤ L / log L ^ C₃ := by
    rw [le_div_iff₀ hlC]
    have := mul_le_mul_of_nonneg_left h1 hpos.le
    have e : (C₀ + A) * ((C₀ + A)⁻¹ * L) = L := by field_simp
    linarith
  have hsplit : L ^ C₀ = L ^ (C₀ + A) * L ^ (-A) := by
    rw [← rpow_add hL0]; ring_nf
  rw [hsplit, rpow_def_of_pos hL0 (C₀ + A)]
  have hA0 : 0 < L ^ (-A) := rpow_pos_of_pos hL0 _
  calc exp (log L * (C₀ + A)) * L ^ (-A) * exp (-(L / log L ^ C₃))
      = L ^ (-A) * exp (log L * (C₀ + A) - L / log L ^ C₃) := by
        rw [sub_eq_add_neg, exp_add]; ring
    _ ≤ L ^ (-A) * exp 0 := by
        gcongr
        linarith
    _ = L ^ (-A) := by rw [exp_zero, mul_one]

/-! ## Arithmetic of the final bounds -/

lemma low_arith {K₁ K₂ Dpw Dmw cV L V M A A₁ B₂ u ℓn : ℝ} (hM : 0 < M) (hL1 : 1 ≤ L)
    (hcV : 0 < cV) (hLV : cV ≤ L * V) (hDp : 0 ≤ Dpw) (hDm : 0 ≤ Dmw) (hB₂ : 0 ≤ B₂)
    (hA₁ : A₁ = A + B₂ + 2) (hu : |u| ≤ 2 * L ^ B₂) (hℓ0 : 0 ≤ ℓn) (hℓ : ℓn ≤ 2 * L) :
    1 / M * ((K₁ * (M * L ^ (-A₁)) + (Dpw / (L * V) + Dmw / (L * V)) * (K₂ * (M * L ^ (-A₁)))) *
      (3 + |u| * ℓn)) ≤ 7 * (|K₁| + (Dpw + Dmw) / cV * |K₂|) * L ^ (-A) := by
  have hL0 : 0 < L := by linarith
  have hLV0 : 0 < L * V := hcV.trans_le hLV
  have hP : 0 < L ^ (-A₁) := rpow_pos_of_pos hL0 _
  have hs : 0 ≤ M * L ^ (-A₁) := by positivity
  set K' := |K₁| + (Dpw + Dmw) / cV * |K₂| with hK'
  have hX : K₁ * (M * L ^ (-A₁)) + (Dpw / (L * V) + Dmw / (L * V)) * (K₂ * (M * L ^ (-A₁))) ≤
      M * L ^ (-A₁) * K' := by
    have e1 : K₁ * (M * L ^ (-A₁)) ≤ |K₁| * (M * L ^ (-A₁)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hs
    have e2 : (Dpw / (L * V) + Dmw / (L * V)) * (K₂ * (M * L ^ (-A₁))) ≤
        (Dpw + Dmw) / cV * (|K₂| * (M * L ^ (-A₁))) := by
      rw [← add_div]
      calc (Dpw + Dmw) / (L * V) * (K₂ * (M * L ^ (-A₁)))
          ≤ (Dpw + Dmw) / (L * V) * (|K₂| * (M * L ^ (-A₁))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hs)
              (by positivity)
        _ ≤ (Dpw + Dmw) / cV * (|K₂| * (M * L ^ (-A₁))) :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) hcV hLV)
              (by positivity)
    rw [hK']
    nlinarith
  have hY0 : 0 ≤ 3 + |u| * ℓn := by positivity
  have hpow1 : 1 ≤ L ^ (B₂ + 1) := one_le_rpow hL1 (by linarith)
  have hY : 3 + |u| * ℓn ≤ 7 * L ^ (B₂ + 1) := by
    have h1 : |u| * ℓn ≤ 2 * L ^ B₂ * (2 * L) :=
      mul_le_mul hu hℓ hℓ0 (by positivity)
    have h2 : 2 * L ^ B₂ * (2 * L) = 4 * L ^ (B₂ + 1) := by
      rw [rpow_add_one hL0.ne']; ring
    linarith
  have hK'0 : 0 ≤ K' := by positivity
  calc 1 / M * ((K₁ * (M * L ^ (-A₁)) + (Dpw / (L * V) + Dmw / (L * V)) *
        (K₂ * (M * L ^ (-A₁)))) * (3 + |u| * ℓn))
      ≤ 1 / M * (M * L ^ (-A₁) * K' * (7 * L ^ (B₂ + 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact (mul_le_mul_of_nonneg_right hX hY0).trans
          (mul_le_mul_of_nonneg_left hY (by positivity))
    _ = 7 * K' * (L ^ (-A₁) * L ^ (B₂ + 1)) := by field_simp
    _ = 7 * K' * L ^ (-A - 1) := by
        rw [← rpow_add hL0, hA₁]; ring_nf
    _ ≤ 7 * K' * L ^ (-A) := by
        refine mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hL1 (by linarith))
          (by positivity)

lemma E_bound {L x u A B₂ C₀ c₀ C₃ T : ℝ} (hL1 : 1 ≤ L) (hx : 0 ≤ x)
    (hu : L ^ B₂ / 2 ≤ |u|) (hB : A + C₀ + 1 ≤ B₂)
    (hE1 : L ^ C₀ * x ^ (-c₀) ≤ L ^ (-A))
    (hE2 : L ^ C₀ * exp (-(L / log L ^ C₃)) ≤ L ^ (-A)) :
    0 ≤ L ^ (-A) + (if |u| ≤ T then L ^ C₀ * (|u|⁻¹ + x ^ (-c₀))
        else L ^ C₀ * exp (-(L / log L ^ C₃))) ∧
    L ^ (-A) + (if |u| ≤ T then L ^ C₀ * (|u|⁻¹ + x ^ (-c₀))
        else L ^ C₀ * exp (-(L / log L ^ C₃))) ≤ 4 * L ^ (-A) := by
  have hL0 : 0 < L := by linarith
  have hA0 : 0 < L ^ (-A) := rpow_pos_of_pos hL0 _
  have hC0 : 0 < L ^ C₀ := rpow_pos_of_pos hL0 _
  have hB0 : 0 < L ^ B₂ := rpow_pos_of_pos hL0 _
  have hx0 : 0 ≤ x ^ (-c₀) := rpow_nonneg hx _
  split_ifs
  · refine ⟨by positivity, ?_⟩
    have hinv : |u|⁻¹ ≤ 2 * L ^ (-B₂) := by
      rw [rpow_neg hL0.le]
      calc |u|⁻¹ ≤ (L ^ B₂ / 2)⁻¹ := inv_anti₀ (by positivity) hu
        _ = 2 * (L ^ B₂)⁻¹ := by field_simp
    have hCB : L ^ C₀ * L ^ (-B₂) ≤ L ^ (-A) := by
      rw [← rpow_add hL0]
      exact rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have : L ^ C₀ * |u|⁻¹ ≤ 2 * L ^ (-A) := by
      calc L ^ C₀ * |u|⁻¹ ≤ L ^ C₀ * (2 * L ^ (-B₂)) := mul_le_mul_of_nonneg_left hinv hC0.le
        _ = 2 * (L ^ C₀ * L ^ (-B₂)) := by ring
        _ ≤ 2 * L ^ (-A) := by linarith
    nlinarith
  · exact ⟨by positivity, by linarith⟩

/-! ## The two frequency ranges -/

open Classical in
/-- Low frequencies `|t| ≤ L^{B₂}`. -/
lemma main_low {γ wPlus C A A₁ B₂ K₁ K₂ cV x M v t : ℝ} {N k : ℕ}
    (χ : DirichletCharacter ℂ k) (J : Set ℝ) (hγ : 0 < γ) (hC : 0 < C) (hM : 0 < M)
    (hL1 : 1 ≤ log x)
    (hx0 : 0 < x) (hV : 0 < mertensProduct (sieveLevel x)) (hcV : 0 < cV)
    (hLV : cV ≤ log x * mertensProduct (sieveLevel x))
    (hrange : ∀ y ∈ Icc M (2 * M), γ ≤ log y / log x ∧ log y / log x < (N + 1) * γ)
    (hwmax : ∀ y ∈ Icc M (2 * M), log y / log x ≤ wPlus) (hwP1 : wPlus ≤ 1)
    (hJ : J.OrdConnected) (hJsub : J ⊆ Icc M (2 * M))
    (h15 : ∀ J' : Set ℝ, J'.OrdConnected → J' ⊆ Icc M (2 * M) →
      ‖(∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
          if (m : ℝ) ∈ J' ∧ IsRough (x ^ γ) m then χ (m : ZMod k) else 0) -
        (if χ = 1 then (((1 / log x) * ∫ y in J', roughDensity γ (log y / log x) : ℝ) : ℂ)
          else 0)‖ ≤ K₁ * (M * log x ^ (-A₁)))
    (h17 : ∀ J' : Set ℝ, J'.OrdConnected → J' ⊆ Icc M (2 * M) →
      ‖(∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
          if (m : ℝ) ∈ J' ∧ IsRough (sieveLevel x) m then χ (m : ZMod k) else 0) -
        (if χ = 1 then ((mertensProduct (sieveLevel x) * (volume J').toReal : ℝ) : ℂ)
          else 0)‖ ≤ K₂ * (M * log x ^ (-A₁)))
    (hB₂C : C + 1 ≤ B₂) (hA₁ : A₁ = A + B₂ + 2) (hv : |v| ≤ log x ^ C)
    (ht : |t| ≤ log x ^ B₂) :
    1 / M * ‖∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1), (if (m : ℝ) ∈ J then
        χ (m : ZMod k) * ((if IsRough (x ^ γ) m then 1 else 0) -
          ((roughDensity γ (log m / log x) /
            (log x * mertensProduct (sieveLevel x)) : ℝ) : ℂ) *
            (if IsRough (sieveLevel x) m then 1 else 0)) else 0) *
        (m : ℂ) ^ (Complex.I * ((t + v : ℝ) : ℂ))‖ ≤
      7 * (|K₁| + (Dp γ N wPlus + Dm γ N wPlus) / cV * |K₂|) * log x ^ (-A) := by
  have hL0 : 0 < log x := by linarith
  have hlf := low_freq hγ N hL0 hV hM hrange hwmax (fun m => χ (m : ZMod k)) (χ = 1)
    (K₁ * (M * log x ^ (-A₁))) (K₂ * (M * log x ^ (-A₁))) h15 h17 J hJ hJsub (t + v)
  have hCB : log x ^ C ≤ log x ^ B₂ := rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hu2 : |t + v| ≤ 2 * log x ^ B₂ := by
    have := abs_add_le t v; linarith
  have h2M : 2 * M ≤ x := by
    have h := hwmax (2 * M) ⟨by linarith, le_rfl⟩
    rw [div_le_iff₀ hL0] at h
    have : log (2 * M) ≤ log x := by nlinarith
    exact (log_le_log_iff (by linarith) hx0).1 this
  have hn : log ((⌊2 * M⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * log x := by
    have hx1 : 1 < x := (log_pos_iff hx0.le).1 hL0
    have hfl : ((⌊2 * M⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * x := by
      push_cast
      have := Nat.floor_le (show (0 : ℝ) ≤ 2 * M by linarith)
      linarith
    calc log ((⌊2 * M⌋₊ + 1 : ℕ) : ℝ) ≤ log (2 * x) := log_le_log (by positivity) hfl
      _ = log 2 + log x := log_mul two_ne_zero hx0.ne'
      _ ≤ 2 * log x := by linarith [log_two_lt_d9]
  have hn0 : 0 ≤ log ((⌊2 * M⌋₊ + 1 : ℕ) : ℝ) := log_natCast_nonneg _
  exact (mul_le_mul_of_nonneg_left hlf (by positivity)).trans
    (low_arith hM hL1 hcV hLV (Dp_nonneg hγ N _) (Dm_nonneg hγ N _) (by linarith) hA₁
      hu2 hn0 hn)

open Classical in
/-- High frequencies `L^{B₂} < |t| ≤ x L^B`. -/
lemma main_high {γ wPlus B C A B₀ B₂ C₀ c₀ C₃ K₃ K₄ x M v t : ℝ} {N k : ℕ}
    (χ : DirichletCharacter ℂ k) (J : Set ℝ) (hγ : 0 < γ) (hC : 0 < C) (hM1 : 1 < M)
    (hL2 : 2 ≤ log x)
    (hx0 : 0 < x) (hV : 0 < mertensProduct (sieveLevel x))
    (hrange : ∀ y ∈ Icc M (2 * M), γ ≤ log y / log x ∧ log y / log x < (N + 1) * γ)
    (hwmax : ∀ y ∈ Icc M (2 * M), log y / log x ≤ wPlus) (hwP0 : 0 < wPlus)
    (hJ : J.OrdConnected) (hJsub : J ⊆ Icc M (2 * M))
    (hHF : log x ^ B₀ ≤ |t + v| → |t + v| ≤ x ^ 2 →
      ‖((1 / M : ℝ) : ℂ) * ∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
        (if (m : ℝ) ∈ J ∧ IsRough (x ^ γ) m then
          χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * ((t + v : ℝ) : ℂ)) else 0)‖ ≤
        K₃ * log x ^ (-A))
    (h19 : ∀ J' : Set ℝ, J'.OrdConnected → J' ⊆ Icc M (2 * M) →
      1 ≤ |t + v| → |t + v| < x ^ 2 →
      ‖((1 / (M * mertensProduct (sieveLevel x)) : ℝ) : ℂ) *
          ∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
            (if (m : ℝ) ∈ J' ∧ IsRough (sieveLevel x) m then
              χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * ((t + v : ℝ) : ℂ)) / ((log m : ℝ) : ℂ)
              else 0)‖ ≤
        K₄ * (log x ^ (-A) +
          if |t + v| ≤ exp (log x / log (log x) ^ 2) then
            log x ^ C₀ * (|t + v|⁻¹ + x ^ (-c₀))
          else log x ^ C₀ * exp (-(log x / log (log x) ^ C₃))))
    (hxx : x * log x ^ B + log x ^ C < x ^ 2)
    (hE1 : log x ^ C₀ * x ^ (-c₀) ≤ log x ^ (-A))
    (hE2 : log x ^ C₀ * exp (-(log x / log (log x) ^ C₃)) ≤ log x ^ (-A))
    (hB₂C : C + 1 ≤ B₂) (hB₂B₀ : B₀ + 1 ≤ B₂) (hB₂A : A + C₀ + 1 ≤ B₂)
    (hv : |v| ≤ log x ^ C) (ht : |t| ≤ x * log x ^ B) (hlow : log x ^ B₂ < |t|) :
    1 / M * ‖∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1), (if (m : ℝ) ∈ J then
        χ (m : ZMod k) * ((if IsRough (x ^ γ) m then 1 else 0) -
          ((roughDensity γ (log m / log x) /
            (log x * mertensProduct (sieveLevel x)) : ℝ) : ℂ) *
            (if IsRough (sieveLevel x) m then 1 else 0)) else 0) *
        (m : ℂ) ^ (Complex.I * ((t + v : ℝ) : ℂ))‖ ≤
      (|K₃| + wPlus * (Dp γ N wPlus + Dm γ N wPlus) * |K₄| * 4) * log x ^ (-A) := by
  have hL0 : 0 < log x := by linarith
  have hL1 : 1 ≤ log x := by linarith
  have hM : 0 < M := by linarith
  have hLA0 : 0 < log x ^ (-A) := rpow_pos_of_pos hL0 _
  have hpow : ∀ a b : ℝ, a + 1 ≤ b → 2 * log x ^ a ≤ log x ^ b := by
    intro a b hab
    have h1 : log x ^ b = log x ^ (b - a) * log x ^ a := by rw [← rpow_add hL0]; ring_nf
    have h2 : log x ≤ log x ^ (b - a) := by
      calc log x = log x ^ (1 : ℝ) := (rpow_one _).symm
        _ ≤ log x ^ (b - a) := rpow_le_rpow_of_exponent_le hL1 (by linarith)
    rw [h1]; nlinarith [rpow_pos_of_pos hL0 a]
  have hulo : log x ^ B₂ / 2 ≤ |t + v| := by
    have := abs_sub_abs_le_abs_sub t (-v)
    rw [abs_neg, sub_neg_eq_add] at this
    linarith [hpow C B₂ hB₂C]
  have huB₀ : log x ^ B₀ ≤ |t + v| := by linarith [hpow B₀ B₂ hB₂B₀]
  have hu1 : 1 ≤ |t + v| := by
    have : log x ≤ log x ^ B₂ := by
      calc log x = log x ^ (1 : ℝ) := (rpow_one _).symm
        _ ≤ log x ^ B₂ := rpow_le_rpow_of_exponent_le hL1 (by linarith)
    linarith
  have hux : |t + v| < x ^ 2 := by
    have := abs_add_le t v; linarith
  have hR := hHF huB₀ hux.le
  obtain ⟨hE0, hE4⟩ := E_bound (T := exp (log x / log (log x) ^ 2)) hL1 hx0.le hulo hB₂A hE1 hE2
  set E := log x ^ (-A) + (if |t + v| ≤ exp (log x / log (log x) ^ 2) then
      log x ^ C₀ * (|t + v|⁻¹ + x ^ (-c₀))
    else log x ^ C₀ * exp (-(log x / log (log x) ^ C₃))) with hE
  have hMV : 0 < M * mertensProduct (sieveLevel x) := mul_pos hM hV
  have h19' : ∀ J' : Set ℝ, J'.OrdConnected → J' ⊆ J →
      ‖∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1), if (m : ℝ) ∈ J' ∧ IsRough (sieveLevel x) m then
        χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * ((t + v : ℝ) : ℂ)) / ((log m : ℝ) : ℂ)
        else 0‖ ≤ M * mertensProduct (sieveLevel x) * (K₄ * E) := by
    intro J' hJ' hsub
    have h := h19 J' hJ' (hsub.trans hJsub) hu1 hux
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.2 hMV)] at h
    have h' := mul_le_mul_of_nonneg_left h hMV.le
    rwa [← mul_assoc, mul_one_div_cancel hMV.ne', one_mul] at h'
  have hP := high_proxy hγ N hL0 hV hM1 hrange hwmax (Finset.range (⌊2 * M⌋₊ + 1))
    (fun m => χ (m : ZMod k)) (t + v) (M * mertensProduct (sieveLevel x) * (K₄ * E)) J hJ
    hJsub h19'
  have hsplit : (∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1), (if (m : ℝ) ∈ J then
      χ (m : ZMod k) * ((if IsRough (x ^ γ) m then 1 else 0) -
        ((roughDensity γ (log m / log x) /
          (log x * mertensProduct (sieveLevel x)) : ℝ) : ℂ) *
          (if IsRough (sieveLevel x) m then 1 else 0)) else 0) *
      (m : ℂ) ^ (Complex.I * ((t + v : ℝ) : ℂ))) =
      (∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1), if (m : ℝ) ∈ J ∧ IsRough (x ^ γ) m then
        χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * ((t + v : ℝ) : ℂ)) else 0) -
      (∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1), if (m : ℝ) ∈ J then
        (if IsRough (sieveLevel x) m then
          χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * ((t + v : ℝ) : ℂ)) else 0) *
          ((roughDensity γ (log m / log x) /
            (log x * mertensProduct (sieveLevel x)) : ℝ) : ℂ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : (m : ℝ) ∈ J
    · simp only [hm, true_and, if_true]
      split_ifs <;> ring
    · simp [hm]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.2 hM)] at hR
  rw [hsplit]
  have hK4E : K₄ * E ≤ |K₄| * (4 * log x ^ (-A)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hE0).trans
      (mul_le_mul_of_nonneg_left hE4 (abs_nonneg _))
  have hDD0 : 0 ≤ Dp γ N wPlus + Dm γ N wPlus :=
    add_nonneg (Dp_nonneg hγ N _) (Dm_nonneg hγ N _)
  have e : 1 / M * ((wPlus * Dp γ N wPlus + wPlus * Dm γ N wPlus) /
      mertensProduct (sieveLevel x) * (M * mertensProduct (sieveLevel x) * (K₄ * E))) =
      wPlus * (Dp γ N wPlus + Dm γ N wPlus) * (K₄ * E) := by
    field_simp
  calc 1 / M * ‖_ - _‖
      ≤ 1 / M * ‖∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1), if (m : ℝ) ∈ J ∧ IsRough (x ^ γ) m then
          χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * ((t + v : ℝ) : ℂ)) else 0‖ +
        1 / M * ((wPlus * Dp γ N wPlus + wPlus * Dm γ N wPlus) /
          mertensProduct (sieveLevel x) * (M * mertensProduct (sieveLevel x) * (K₄ * E))) := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add le_rfl hP))
          (one_div_pos.2 hM).le
    _ ≤ K₃ * log x ^ (-A) + wPlus * (Dp γ N wPlus + Dm γ N wPlus) * (K₄ * E) := by
        rw [e]; linarith
    _ ≤ |K₃| * log x ^ (-A) +
          wPlus * (Dp γ N wPlus + Dm γ N wPlus) * (|K₄| * (4 * log x ^ (-A))) :=
        add_le_add (mul_le_mul_of_nonneg_right (le_abs_self _) hLA0.le)
          (mul_le_mul_of_nonneg_left hK4E (mul_nonneg hwP0.le hDD0))
    _ = (|K₃| + wPlus * (Dp γ N wPlus + Dm γ N wPlus) * |K₄| * 4) * log x ^ (-A) := by ring

end ArtinPrimitiveRoots.A106R

namespace ArtinPrimitiveRoots

open Real MeasureTheory Set Filter Topology A106R

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real MeasureTheory Set Filter Topology A106R
open Classical in
theorem solution (C γ wMinus wPlus : ℝ) (hC : 0 < C) (hγ : 0 < γ)
    (hγw : γ < wMinus) (hww : wMinus < wPlus) (hwPlus : wPlus < 1) :
    ∀ A₀ B A : ℝ, 0 < A₀ → 0 < B → 0 < A →
      ∃ C' : ℝ, ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ Hm : ℝ, wMinus ≤ log Hm / log x → log (2 * Hm) / log x ≤ wPlus →
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc Hm (2 * Hm) →
      ∀ v : ℝ, |v| ≤ log x ^ C →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
      ∀ t : ℝ, |t| ≤ x * log x ^ B →
        ‖((1 / Hm : ℝ) : ℂ) * ∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1),
            (if (m : ℝ) ∈ J then
              (m : ℂ) ^ (Complex.I * v) *
                ((if IsRough (x ^ γ) m then 1 else 0) -
                  ((roughDensity γ (log m / log x) /
                      (log x * mertensProduct (sieveLevel x)) : ℝ) : ℂ) *
                    (if IsRough (sieveLevel x) m then 1 else 0))
            else 0) * χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * t)‖ ≤ C' * log x ^ (-A) := by
  intro A₀ B A hA₀ hB hA
  have hw0 : 0 < wMinus := hγ.trans hγw
  have hwP0 : 0 < wPlus := hw0.trans hww
  -- constants from the cuts, in the paper's order: A, then A₄ = A and A₃ = A, then B₂, A₁
  obtain ⟨C₃, -, h19all⟩ := rough_twisted_log_weighted_bound
  obtain ⟨C₀, c₀, hC₀, hc₀, h19A⟩ := h19all wMinus wPlus hw0 hww hwPlus A₀ hA₀
  obtain ⟨K₄, x₄, h19⟩ := h19A A hA
  clear h19A h19all
  obtain ⟨B₀, K₃, x₃, hHF⟩ :=
    rough_prime_product_high_frequency γ wMinus wPlus hγ hγw hww hwPlus A₀ A hA₀ hA
  obtain ⟨B₂, hB₂C, hB₂B₀, hB₂A⟩ :
      ∃ B₂ : ℝ, C + 1 ≤ B₂ ∧ B₀ + 1 ≤ B₂ ∧ A + C₀ + 1 ≤ B₂ :=
    ⟨max (max C B₀) (A + C₀) + 1, by
      have := le_max_left (max C B₀) (A + C₀); have := le_max_left C B₀; linarith, by
      have := le_max_left (max C B₀) (A + C₀); have := le_max_right C B₀; linarith, by
      have := le_max_right (max C B₀) (A + C₀); linarith⟩
  obtain ⟨K₁, x₁, h15⟩ := rough_prime_product_count γ wMinus wPlus hγ hγw hww hwPlus A₀
    (A + B₂ + 2) hA₀ (by linarith)
  obtain ⟨K₂, x₂, h17⟩ := rough_count_character wMinus wPlus hw0 hww hwPlus A₀
    (A + B₂ + 2) hA₀ (by linarith)
  obtain ⟨N, hNγ⟩ : ∃ N : ℕ, wPlus < (N + 1) * γ := by
    obtain ⟨N, hN⟩ := exists_nat_gt (wPlus / γ)
    refine ⟨N, ?_⟩
    rw [div_lt_iff₀ hγ] at hN
    nlinarith
  have hcV0 : 0 < exp (-eulerMascheroniConstant) / 2 := by positivity
  have hDD0 : 0 ≤ Dp γ N wPlus + Dm γ N wPlus :=
    add_nonneg (Dp_nonneg hγ N _) (Dm_nonneg hγ N _)
  -- the conditions on x
  have hev : ∀ᶠ x in atTop, (x₁ ≤ x ∧ x₂ ≤ x ∧ x₃ ≤ x ∧ x₄ ≤ x) ∧ 0 < x ∧ 2 ≤ log x ∧
      x * log x ^ B + log x ^ C < x ^ 2 ∧
      (0 < mertensProduct (sieveLevel x) ∧
        exp (-eulerMascheroniConstant) / 2 ≤ log x * mertensProduct (sieveLevel x)) ∧
      log x ^ C₀ * x ^ (-c₀) ≤ log x ^ (-A) ∧
      log x ^ C₀ * exp (-(log x / log (log x) ^ C₃)) ≤ log x ^ (-A) := by
    filter_upwards [eventually_ge_atTop x₁, eventually_ge_atTop x₂, eventually_ge_atTop x₃,
      eventually_ge_atTop x₄, eventually_gt_atTop 0, tendsto_log_atTop.eventually_ge_atTop 2,
      ev_poly B C, ev_mertens, ev_E1 C₀ c₀ A hc₀, ev_E2 C₀ C₃ A (by linarith)]
      with x h1 h2 h3 h4 h0 h5 h6 h7 h8 h9
    exact ⟨⟨h1, h2, h3, h4⟩, h0, h5, h6, h7, h8, h9⟩
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hev
  refine ⟨max (7 * (|K₁| + (Dp γ N wPlus + Dm γ N wPlus) /
      (exp (-eulerMascheroniConstant) / 2) * |K₂|))
    (|K₃| + wPlus * (Dp γ N wPlus + Dm γ N wPlus) * |K₄| * 4), x₀,
    fun x hx M hM1 hM2 J hJ hJsub v hv k hk hkA χ t ht => ?_⟩
  obtain ⟨⟨hx1, hx2, hx3, hx4⟩, hx0, hL2, hxx, ⟨hV, hLV⟩, hE1, hE2⟩ := hx₀ x hx
  have hL0 : 0 < log x := by linarith
  have hLA0 : 0 < log x ^ (-A) := rpow_pos_of_pos hL0 _
  have hC'0 : 0 ≤ 7 * (|K₁| + (Dp γ N wPlus + Dm γ N wPlus) /
      (exp (-eulerMascheroniConstant) / 2) * |K₂|) := by positivity
  -- the degenerate case `M ≤ 0`: the interval is empty
  by_cases hM : 0 < M
  swap
  · have hM0 : M ≠ 0 := by
      rintro rfl
      simp only [log_zero, zero_div] at hM1
      linarith
    have hneg : M < 0 := lt_of_le_of_ne (not_lt.1 hM) hM0
    have hJe : ∀ y, y ∉ J := fun y hy => by
      have := hJsub hy
      simp only [mem_Icc] at this
      linarith [this.1, this.2]
    simp only [hJe, if_false, zero_mul, Finset.sum_const_zero, mul_zero, norm_zero]
    exact mul_nonneg (le_max_of_le_left hC'0) hLA0.le
  -- the main case
  have hlogM : wMinus * log x ≤ log M := (le_div_iff₀ hL0).1 hM1
  have hM1' : 1 < M := (log_pos_iff hM.le).1 (by nlinarith)
  have hrange : ∀ y ∈ Icc M (2 * M),
      γ ≤ log y / log x ∧ log y / log x < (N + 1) * γ := by
    intro y hy
    have h1 : log M ≤ log y := log_le_log hM hy.1
    have h2 : log y ≤ log (2 * M) := log_le_log (by linarith [hy.1]) hy.2
    have h2' : log (2 * M) ≤ wPlus * log x := (div_le_iff₀ hL0).1 hM2
    have h3 : γ * log x ≤ wMinus * log x := mul_le_mul_of_nonneg_right hγw.le hL0.le
    have h4 : wPlus * log x < (N + 1) * γ * log x := mul_lt_mul_of_pos_right hNγ hL0
    constructor
    · rw [le_div_iff₀ hL0]; linarith
    · rw [div_lt_iff₀ hL0]; linarith
  have hwmax : ∀ y ∈ Icc M (2 * M), log y / log x ≤ wPlus := by
    intro y hy
    have h2 : log y ≤ log (2 * M) := log_le_log (by linarith [hy.1]) hy.2
    have h2' : log (2 * M) ≤ wPlus * log x := (div_le_iff₀ hL0).1 hM2
    rw [div_le_iff₀ hL0]; linarith
  -- rewrite the twisted sum with `u = t + v`
  have hsum_eq : (∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
        (if (m : ℝ) ∈ J then
          (m : ℂ) ^ (Complex.I * v) *
            ((if IsRough (x ^ γ) m then 1 else 0) -
              ((roughDensity γ (log m / log x) /
                (log x * mertensProduct (sieveLevel x)) : ℝ) : ℂ) *
                (if IsRough (sieveLevel x) m then 1 else 0))
        else 0) * χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * t)) =
      ∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1), (if (m : ℝ) ∈ J then
        χ (m : ZMod k) * ((if IsRough (x ^ γ) m then 1 else 0) -
          ((roughDensity γ (log m / log x) /
            (log x * mertensProduct (sieveLevel x)) : ℝ) : ℂ) *
            (if IsRough (sieveLevel x) m then 1 else 0)) else 0) *
        (m : ℂ) ^ (Complex.I * ((t + v : ℝ) : ℂ)) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : (m : ℝ) ∈ J
    · have hmpos : (0 : ℝ) < m := hM.trans_le (hJsub hm).1
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hmpos.ne'
      have hcpow : (m : ℂ) ^ (Complex.I * ((t + v : ℝ) : ℂ)) =
          (m : ℂ) ^ (Complex.I * v) * (m : ℂ) ^ (Complex.I * t) := by
        rw [← Complex.cpow_add _ _ hm0]; push_cast; ring_nf
      simp only [hm, if_true]
      rw [hcpow]; ring
    · simp [hm]
  rw [hsum_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.2 hM)]
  by_cases hlow : |t| ≤ log x ^ B₂
  · exact (main_low χ J hγ hC hM (by linarith) hx0 hV hcV0 hLV hrange hwmax hwPlus.le hJ hJsub
      (h15 x hx1 M hM hM1 hM2 k hk hkA χ) (h17 x hx2 M hM hM1 hM2 k hk hkA χ) hB₂C rfl hv
      hlow).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hLA0.le)
  · push Not at hlow
    exact (main_high χ J hγ hC hM1' hL2 hx0 hV hrange hwmax hwP0 hJ hJsub
      (hHF x hx3 M hM hM1 hM2 k hk hkA χ J hJ hJsub (t + v))
      (fun J' hJ' hJ'sub hu1 hux => h19 x hx4 M hM hM1 hM2 k hk hkA χ J' hJ' hJ'sub (t + v)
        hu1 hux)
      hxx hE1 hE2 hB₂C hB₂B₀ hB₂A hv ht hlow).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hLA0.le)
end
