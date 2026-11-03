-- Prove2me | Definitions.Def_LeanLevy_Fourier_Bochner
-- name    : LeanLevy_Fourier_Bochner
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-31T10:21:15.512492+00:00
-- url     : https://prove2.me/theorems/b731418e-7219-4644-9d72-59a3c64f89b6
-- title:
--   LeanLevy source module: Fourier.Bochner
-- statement:
--   Source-faithful, comment-compacted copy of the pinned LeanLevy module LeanLevy.Fourier.Bochner. It retains the module's helper declarations and complete Gaussian-smoothing proof of ProbabilityTheory.bochner, with imports mapped to the corresponding definitions in this mission. Prove2Me remote verification is pending.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Fourier/Bochner.lean

import Definitions.Def_LeanLevy_Fourier_PositiveDefinite
import Definitions.Def_LeanLevy_Fourier_MeasureFourier
import Definitions.Def_LeanLevy_Probability_WeakConvergence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory Complex ComplexConjugate Filter Topology Set Function
open scoped NNReal ENNReal FourierTransform RealInnerProductSpace
namespace ProbabilityTheory
private theorem intervalIntegral_eq_zero_of_forall_eq_zero {a b : ℝ} {f : ℝ → ℝ}
    (hf : ∀ t, t ∈ Set.uIoo a b → f t = 0) :
    ∫ t in a..b, f t = 0 := by
  rcases le_or_gt a b with hab | hab
  · rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact fun t ht => hf t (Set.uIoo_of_le hab ▸ ht)
  · rw [intervalIntegral.integral_symm, neg_eq_zero,
      intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact fun t ht => hf t (Set.uIoo_comm a b ▸ Set.uIoo_of_le hab.le ▸ ht)
private noncomputable def inverseFourierDensity (ψ : ℝ → ℂ) (x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (∫ u, ψ u * exp (-(↑x * ↑u * I))).re
private noncomputable def fejerApproximant (ψ : ℝ → ℂ) (N : ℝ) (x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (∫ u in Set.Icc (-N) N,
      ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / N))).re
private theorem isPositiveDefinite_mul_exp (ψ : ℝ → ℂ) (hpd : IsPositiveDefinite ψ) (x : ℝ) :
    IsPositiveDefinite (fun u => ψ u * exp (-(↑x * ↑u * I))) := by
  have hexp_pd : IsPositiveDefinite (fun u => exp (-(↑x * ↑u * I))) := by
    intro n pts c
    have hsum_eq : ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        exp (-(↑x * ↑(pts i - pts j) * I)) =
        ↑(Complex.normSq (∑ i, c i * exp (↑x * ↑(pts i) * I))) := by
      rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [map_mul, ← exp_conj, conj_ofReal, conj_I, mul_neg]
      rw [show -(↑x * ↑(pts i - pts j) * I) =
          -(↑x * ↑(pts i) * I) + ↑x * ↑(pts j) * I from by push_cast; ring,
        exp_add]
      ring
    rw [hsum_eq]
    exact_mod_cast Complex.normSq_nonneg _
  exact hpd.mul hexp_pd
private theorem riemannSum_nonneg_of_pd (g : ℝ → ℂ) (hg_pd : IsPositiveDefinite g)
    (N : ℝ) (hN : 0 < N) (m : ℕ) :
    0 ≤ (N / ((m : ℝ) + 1)) ^ 2 / N *
      (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        g ((i : ℝ) * (N / ((m : ℝ) + 1)) - (j : ℝ) * (N / ((m : ℝ) + 1)))).re := by
  apply mul_nonneg
  · exact div_nonneg (sq_nonneg _) hN.le
  · have h := hg_pd (m + 1)
      (fun i => (i : ℝ) * (N / ((m : ℝ) + 1))) (fun _ => 1)
    simp only [map_one, one_mul] at h
    exact (Complex.nonneg_iff.mp h).1
set_option maxHeartbeats 800000 in
private theorem tent_integral_eq_fubini (g : ℝ → ℂ) (hg_cont : Continuous g)
    (N : ℝ) (hN : 0 < N) :
    (∫ u in Set.Icc (-N) N,
      g u * (1 - ↑(|u| / N))).re =
    (1 / N) * ∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, (g (s - t)).re := by
  have hf_int : Integrable (fun u => g u * (1 - ↑(|u| / N : ℝ) : ℂ))
      (volume.restrict (Set.Icc (-N) N)) :=
    (hg_cont.mul (continuous_const.sub
      (continuous_ofReal.comp
        ((continuous_abs.comp continuous_id).div_const N)))).continuousOn.integrableOn_Icc
  have hLHS : (∫ u in Set.Icc (-N) N,
      g u * (1 - ↑(|u| / N))).re =
      ∫ u in Set.Icc (-N) N, (g u).re * (1 - |u| / N) := by
    calc (∫ u in Set.Icc (-N) N,
            g u * (1 - ↑(|u| / N))).re
        = ∫ u in Set.Icc (-N) N,
            (g u * (1 - ↑(|u| / N))).re :=
            (integral_re hf_int).symm
      _ = ∫ u in Set.Icc (-N) N, (g u).re * (1 - |u| / N) := by
            congr 1; ext u
            have : (1 : ℂ) - ↑(|u| / N) = ↑((1 : ℝ) - |u| / N) := by push_cast; ring
            rw [this, re_mul_ofReal]
  rw [hLHS]
  set F : ℝ → ℝ → ℝ := fun s t => (g (s - t)).re with hF_def
  have hF_cts : Continuous F.uncurry :=
    (Complex.continuous_re.comp hg_cont).comp (continuous_fst.sub continuous_snd)
  have hfub : ∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t =
      ∫ u in Set.Icc (-N) N, (g u).re * (N - |u|) := by
    have hint : Integrable F.uncurry
        ((volume.restrict (Set.Icc 0 N)).prod (volume.restrict (Set.Icc 0 N))) := by
      rw [Measure.prod_restrict]
      exact hF_cts.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hswap : ∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t =
        ∫ t in Set.Icc 0 N, ∫ s in Set.Icc 0 N, F s t :=
      integral_integral_swap hint
    rw [hswap]
    have hinner2 : ∀ t ∈ Set.Icc (0:ℝ) N, ∫ s in Set.Icc 0 N, F s t =
        ∫ u in (-t)..(N - t), (g u).re := by
      intro t _
      simp only [F]
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hN.le,
          intervalIntegral.integral_comp_sub_right (fun u => (g u).re) t]
      congr 1; ring
    rw [setIntegral_congr_fun measurableSet_Icc hinner2]
    have hlhs_ext : ∫ t in Set.Icc 0 N, ∫ u in (-t)..(N - t), (g u).re =
        ∫ t in (0 : ℝ)..N, ∫ u in Set.Icc (-N) N,
          (g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hN.le]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hN.le] at ht
      have hsubset : Set.Icc (-t) (N - t) ⊆ Set.Icc (-N) N :=
        fun u ⟨h1, h2⟩ => ⟨by linarith [ht.2], by linarith [ht.1]⟩
      show ∫ u in (-t)..(N - t), (g u).re =
        ∫ u in Set.Icc (-N) N, (g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u
      rw [intervalIntegral.integral_of_le (show -t ≤ N - t by linarith [ht.1]),
          ← integral_Icc_eq_integral_Ioc]
      conv_rhs =>
        arg 2; ext u
        rw [show (g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u =
            Set.indicator (Set.Icc (-t) (N - t)) (fun u => (g u).re) u from by
          simp [Set.indicator_apply]]
      rw [setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.mpr hsubset]
    rw [hlhs_ext]
    have hmeas_ind : Measurable (fun p : ℝ × ℝ =>
        (g p.2).re * Set.indicator (Set.Icc (-p.1) (N - p.1)) 1 p.2) :=
      ((Complex.continuous_re.comp hg_cont).measurable.comp measurable_snd).mul
        (Measurable.indicator measurable_const
          ((measurableSet_le (measurable_neg.comp measurable_fst) measurable_snd).inter
           (measurableSet_le measurable_snd (measurable_const.sub measurable_fst))))
    have h_re_int : Integrable (fun u => (g u).re)
        (volume.restrict (Set.Icc (-N) N)) :=
      (Complex.continuous_re.comp hg_cont).continuousOn.integrableOn_Icc
    haveI : IsFiniteMeasure (volume.restrict (Set.uIoc 0 N)) :=
      ⟨by simp [Real.volume_uIoc, abs_of_nonneg hN.le]⟩
    have hint_prod : Integrable
        (uncurry fun t u => (g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u)
        ((volume.restrict (Set.uIoc 0 N)).prod
         (volume.restrict (Set.Icc (-N) N))) :=
      (h_re_int.comp_snd (volume.restrict (Set.uIoc 0 N))).mono
        hmeas_ind.aestronglyMeasurable (ae_of_all _ fun ⟨t, u⟩ => by
          simp only [uncurry]
          calc ‖(g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u‖
              ≤ ‖(g u).re‖ * ‖Set.indicator (Set.Icc (-t) (N - t)) (1 : ℝ → ℝ) u‖ :=
                norm_mul_le _ _
            _ ≤ ‖(g u).re‖ * 1 := by
                apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
                simp [Set.indicator_apply]; split_ifs <;> simp
            _ = ‖(g u).re‖ := mul_one _)
    rw [intervalIntegral_integral_swap hint_prod]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp only
    have huN_bound : |u| ≤ N := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
    have hcond_swap : ∀ t : ℝ,
        Set.indicator (Set.Icc (-t) (N - t)) (1 : ℝ → ℝ) u =
        Set.indicator (Set.Icc (-u) (N - u)) 1 t := fun t => by
      simp only [Set.indicator_apply, Set.mem_Icc]
      exact ite_congr
        (propext ⟨fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩,
                 fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩⟩)
        (fun _ => rfl) (fun _ => rfl)
    rw [show ∫ t in (0 : ℝ)..N,
            (g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u =
        (g u).re * ∫ t in (0 : ℝ)..N,
            Set.indicator (Set.Icc (-t) (N - t)) (1 : ℝ → ℝ) u from
      intervalIntegral.integral_const_mul _ _]
    congr 1
    simp_rw [hcond_swap]
    rcases le_or_gt u 0 with hu0 | hu0
    ·
      have hint1 : IntervalIntegrable (Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ))
          volume 0 (-u) :=
        (integrable_indicator_iff measurableSet_Icc |>.mpr (integrableOn_const isCompact_Icc.measure_lt_top.ne)).intervalIntegrable
      have hint2 : IntervalIntegrable (Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ))
          volume (-u) N :=
        (integrable_indicator_iff measurableSet_Icc |>.mpr (integrableOn_const isCompact_Icc.measure_lt_top.ne)).intervalIntegrable
      rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
      rw [show ∫ t in (0 : ℝ)..(-u),
              Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ) t = 0 from
          intervalIntegral_eq_zero_of_forall_eq_zero fun t ht => by
            rw [Set.uIoo_of_le (by linarith [hu0])] at ht
            simp [Set.mem_Icc,
                  show ¬(-u ≤ t) from by linarith [ht.2]]]
      have hnu_le_N : -u ≤ N := by
        rw [abs_of_nonpos hu0] at huN_bound; linarith
      rw [show ∫ t in (-u)..N,
              Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ) t =
          ∫ t in (-u)..N, (1 : ℝ) from
          intervalIntegral.integral_congr fun t ht => by
            rw [Set.uIcc_of_le hnu_le_N] at ht
            simp [Set.mem_Icc, ht.1,
                  show t ≤ N - u from by linarith [hu0, ht.2]]]
      simp [intervalIntegral.integral_const, abs_of_nonpos hu0]
    ·
      have huN : u ≤ N := by
        rw [abs_of_pos hu0] at huN_bound; exact huN_bound
      have hint1 : IntervalIntegrable (Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ))
          volume 0 (N - u) :=
        (integrable_indicator_iff measurableSet_Icc |>.mpr (integrableOn_const isCompact_Icc.measure_lt_top.ne)).intervalIntegrable
      have hint2 : IntervalIntegrable (Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ))
          volume (N - u) N :=
        (integrable_indicator_iff measurableSet_Icc |>.mpr (integrableOn_const isCompact_Icc.measure_lt_top.ne)).intervalIntegrable
      rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
      rw [show ∫ t in (0 : ℝ)..(N - u),
              Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ) t =
          ∫ t in (0 : ℝ)..(N - u), (1 : ℝ) from
          intervalIntegral.integral_congr fun t ht => by
            rw [Set.uIcc_of_le (by linarith [huN])] at ht
            simp [Set.mem_Icc,
                  show -u ≤ t from by linarith [ht.1, hu0.le], ht.2]]
      rw [show ∫ t in (N - u)..N,
              Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ) t = 0 from
          intervalIntegral_eq_zero_of_forall_eq_zero fun t ht => by
            rw [Set.uIoo_of_le (by linarith [huN])] at ht
            simp [Set.mem_Icc, show ¬(t ≤ N - u) from by
              linarith [ht.1]]]
      simp [intervalIntegral.integral_const, abs_of_pos hu0]
  rw [hfub, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  dsimp only
  have huN_abs : |u| ≤ N := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
  field_simp [hN.ne']
set_option maxHeartbeats 800000 in
private theorem tendsto_riemannSum_of_uniformContinuousOn
    (F : ℝ → ℝ → ℝ) (N : ℝ) (hN : 0 < N)
    (hF_cts : Continuous F.uncurry)
    (hF_ucont : UniformContinuousOn F.uncurry
        (Set.Icc 0 N ×ˢ Set.Icc 0 N)) :
    Tendsto (fun m : ℕ => (N / ((m : ℝ) + 1)) ^ 2 *
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        F ((i : ℝ) * (N / ((m : ℝ) + 1))) ((j : ℝ) * (N / ((m : ℝ) + 1))))
      atTop (𝓝 (∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.uniformContinuousOn_iff] at hF_ucont
  obtain ⟨δ, hδ_pos, hδ⟩ := hF_ucont (ε / 2 / N ^ 2) (by positivity)
  have hδ' : 0 < δ / Real.sqrt 2 := by positivity
  refine ⟨⌈N / (δ / Real.sqrt 2)⌉₊, fun m hm => ?_⟩
  set h := N / ((m : ℝ) + 1) with hh_def
  have hh_pos : (0 : ℝ) < h := div_pos hN (by positivity)
  have hh_small : h < δ / Real.sqrt 2 := by
    have hM_le : (⌈N / (δ / Real.sqrt 2)⌉₊ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hM_pos : (0 : ℝ) < ⌈N / (δ / Real.sqrt 2)⌉₊ := by
      exact_mod_cast Nat.ceil_pos.mpr (by positivity)
    calc h = N / ((m : ℝ) + 1) := hh_def
        _ < N / (⌈N / (δ / Real.sqrt 2)⌉₊ : ℝ) := by
            apply div_lt_div_of_pos_left hN (by exact_mod_cast hM_pos)
            linarith
        _ ≤ N / (N / (δ / Real.sqrt 2)) := by
            apply div_le_div_of_nonneg_left hN.le (by positivity)
            exact_mod_cast Nat.le_ceil _
        _ = δ / Real.sqrt 2 := by field_simp [hN.ne']
  have hbox_split : ∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t =
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
        ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h), F s t := by
    have hN_eq : N = (m + 1 : ℝ) * h := by push_cast [hh_def]; field_simp
    have hφ_cont : Continuous (fun s => ∫ t in Set.Icc 0 N, F s t) :=
      continuous_parametric_integral_of_continuous hF_cts isCompact_Icc
    have h_Icc_split : ∀ (φ : ℝ → ℝ), ContinuousOn φ (Set.Icc 0 N) →
        ∫ u in Set.Icc 0 N, φ u =
        ∑ i : Fin (m + 1), ∫ u in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h), φ u := by
      intro φ hφ
      have h_a_def : ∀ k : ℕ, (k : ℝ) * h = (fun k : ℕ => (k : ℝ) * h) k := fun k => rfl
      rw [show (0 : ℝ) = (↑(0 : ℕ)) * h from by simp, hN_eq,
          show (↑m + (1 : ℝ)) * h = (↑(m + 1 : ℕ) : ℝ) * h from by push_cast; ring,
          integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by push_cast; nlinarith [hh_pos])]
      rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico
        (a := fun k : ℕ => (k : ℝ) * h) (Nat.zero_le _)
        (fun k hk =>
          (hφ.mono (Set.Icc_subset_Icc (by positivity)
            (by rw [hN_eq]; apply mul_le_mul_of_nonneg_right _ hh_pos.le
                have : k + 1 ≤ m + 1 := hk.2
                exact_mod_cast this))).intervalIntegrable_of_Icc
            (by push_cast; linarith [hh_pos, hk.1]))]
      rw [Nat.Ico_zero_eq_range, ← Fin.sum_univ_eq_sum_range]
      congr 1; ext i; push_cast
      rw [intervalIntegral.integral_of_le (by nlinarith [hh_pos]),
          ← integral_Icc_eq_integral_Ioc]
    rw [h_Icc_split _ hφ_cont.continuousOn]
    congr 1; ext i
    rw [show ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
            ∫ t in Set.Icc 0 N, F s t =
        ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
          ∑ j : Fin (m + 1), ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
          F s t from by
      apply setIntegral_congr_fun measurableSet_Icc
      intro s _
      exact h_Icc_split (fun t => F s t)
        (hF_cts.comp (continuous_const.prodMk continuous_id)).continuousOn]
    rw [integral_finsetSum (Finset.univ : Finset (Fin (m + 1))) (fun (j : Fin (m + 1)) _ =>
      (continuous_parametric_integral_of_continuous hF_cts
        (isCompact_Icc (a := (j : ℝ) * h) (b := ((j : ℝ) + 1) * h))).continuousOn.integrableOn_Icc)]
  rw [Real.dist_eq, hbox_split]
  calc |((N / ((m : ℝ) + 1)) ^ 2 * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
          F ((i : ℝ) * h) ((j : ℝ) * h)) -
        ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
          ∫ s in Set.Icc (↑i * h) ((↑i + 1) * h),
          ∫ t in Set.Icc (↑j * h) ((↑j + 1) * h), F s t|
      = |∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
          (h ^ 2 * F ((i : ℝ) * h) ((j : ℝ) * h) -
           ∫ s in Set.Icc (↑i * h) ((↑i + 1) * h),
           ∫ t in Set.Icc (↑j * h) ((↑j + 1) * h), F s t)| := by
        congr 1
        simp_rw [← hh_def, Finset.mul_sum, ← Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
          |h ^ 2 * F ((i : ℝ) * h) ((j : ℝ) * h) -
           ∫ s in Set.Icc (↑i * h) ((↑i + 1) * h),
           ∫ t in Set.Icc (↑j * h) ((↑j + 1) * h), F s t| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin (m + 1), ∑ _j : Fin (m + 1), h ^ 2 * (ε / 2 / N ^ 2) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        have hile : (i : ℝ) * h ≤ ((i : ℝ) + 1) * h := by nlinarith [hh_pos]
        have hjle : (j : ℝ) * h ≤ ((j : ℝ) + 1) * h := by nlinarith [hh_pos]
        have hN_eq' : N = (↑m + 1) * h := by rw [hh_def]; field_simp
        have hi_bound : ((i : ℝ) + 1) * h ≤ N := by
          rw [hN_eq']; apply mul_le_mul_of_nonneg_right _ hh_pos.le
          have := i.2; exact_mod_cast this
        have hj_bound : ((j : ℝ) + 1) * h ≤ N := by
          rw [hN_eq']; apply mul_le_mul_of_nonneg_right _ hh_pos.le
          have := j.2; exact_mod_cast this
        have hi_nn : (0 : ℝ) ≤ (i : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh_pos.le
        have hj_nn : (0 : ℝ) ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh_pos.le
        have hint_const_j : IntegrableOn (fun _ => F ((i : ℝ) * h) ((j : ℝ) * h))
            (Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h)) :=
          integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)
        have hint_F_inner : ∀ s : ℝ, IntegrableOn (fun t => F s t)
            (Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h)) := fun s =>
          (hF_cts.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc
        have hint_const_i : IntegrableOn
            (fun s => ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
              F ((i : ℝ) * h) ((j : ℝ) * h))
            (Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h)) :=
          integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)
        have hint_F_outer : IntegrableOn
            (fun s => ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h), F s t)
            (Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h)) :=
          (continuous_parametric_integral_of_continuous hF_cts
            (isCompact_Icc (a := (j : ℝ) * h) (b := ((j : ℝ) + 1) * h))).continuousOn.integrableOn_Icc
        have heq : h ^ 2 * F ((i : ℝ) * h) ((j : ℝ) * h) -
            ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
            ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h), F s t =
            ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
            ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
            (F ((i : ℝ) * h) ((j : ℝ) * h) - F s t) := by
          rw [show h ^ 2 * F ((i : ℝ) * h) ((j : ℝ) * h) =
              ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
              ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
              F ((i : ℝ) * h) ((j : ℝ) * h) from by
            simp only [setIntegral_const, smul_eq_mul,
              Real.volume_real_Icc_of_le hile, Real.volume_real_Icc_of_le hjle]
            ring]
          rw [← integral_sub hint_const_i hint_F_outer]
          congr 1; ext s
          rw [← integral_sub hint_const_j (hint_F_inner s)]
        rw [heq]
        have hint_diff_outer : IntegrableOn
            (fun s => ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
              (F ((i : ℝ) * h) ((j : ℝ) * h) - F s t))
            (Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h)) := by
          have := hint_const_i.sub hint_F_outer
          simp only [integral_sub hint_const_j (hint_F_inner _)] at this ⊢
          exact this
        calc |∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
                ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
                (F ((i : ℝ) * h) ((j : ℝ) * h) - F s t)|
            ≤ ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
              ‖∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
                (F ((i : ℝ) * h) ((j : ℝ) * h) - F s t)‖ :=
                by rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
          _ ≤ ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
              ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
              ε / 2 / N ^ 2 := by
              apply setIntegral_mono_on hint_diff_outer.norm
                (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne))
                measurableSet_Icc
              intro s hs
              apply le_trans (norm_integral_le_integral_norm _)
              apply setIntegral_mono_on (hint_const_j.sub (hint_F_inner s)).norm
                (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne))
                measurableSet_Icc
              intro t ht
              simp only [Pi.sub_apply, Real.norm_eq_abs]
              rw [show |F ((i : ℝ) * h) ((j : ℝ) * h) - F s t| =
                  dist (uncurry F ((i : ℝ) * h, (j : ℝ) * h))
                       (uncurry F (s, t)) from by
                simp [uncurry, Real.dist_eq]]
              apply le_of_lt
              apply hδ
              · exact ⟨⟨hi_nn, by linarith [hi_bound]⟩,
                      ⟨hj_nn, by linarith [hj_bound]⟩⟩
              · exact ⟨⟨hi_nn.trans hs.1, hs.2.trans (by linarith [hi_bound])⟩,
                      ⟨hj_nn.trans ht.1, ht.2.trans (by linarith [hj_bound])⟩⟩
              · rw [Prod.dist_eq]
                have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
                have hsqrt2_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := by
                  rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
                calc max (dist ((i : ℝ) * h) s) (dist ((j : ℝ) * h) t)
                    ≤ Real.sqrt 2 * h := by
                      apply max_le
                      · rw [Real.dist_eq, abs_le]
                        exact ⟨by nlinarith [hs.2, hsqrt2_ge_one],
                               by nlinarith [hs.1, hsqrt2_pos]⟩
                      · rw [Real.dist_eq, abs_le]
                        exact ⟨by nlinarith [ht.2, hsqrt2_ge_one],
                               by nlinarith [ht.1, hsqrt2_pos]⟩
                  _ < δ := by
                      have : Real.sqrt 2 * h < Real.sqrt 2 * (δ / Real.sqrt 2) :=
                        mul_lt_mul_of_pos_left hh_small hsqrt2_pos
                      rwa [mul_div_cancel₀ _ hsqrt2_pos.ne'] at this
          _ = h ^ 2 * (ε / 2 / N ^ 2) := by
              simp only [setIntegral_const, smul_eq_mul,
                Real.volume_real_Icc_of_le hile, Real.volume_real_Icc_of_le hjle]
              ring
    _ = ε / 2 := by
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        have hm1_pos : (0 : ℝ) < ↑m + 1 := by positivity
        rw [hh_def]
        push_cast
        field_simp [hm1_pos.ne']
    _ < ε := by linarith
set_option maxHeartbeats 800000 in
private theorem fejerApproximant_nonneg (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (N : ℝ) (hN : 0 < N) (x : ℝ) : 0 ≤ fejerApproximant ψ N x := by
  unfold fejerApproximant
  apply mul_nonneg
  · apply div_nonneg one_pos.le
    exact mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos |>.le
  ·
    set g : ℝ → ℂ := fun u => ψ u * exp (-(↑x * ↑u * I)) with hg_def
    have hg_pd : IsPositiveDefinite g := isPositiveDefinite_mul_exp ψ hpd x
    have hg_cont : Continuous g :=
      hψc.mul (((continuous_const.mul continuous_ofReal).mul continuous_const).neg.cexp)
    set R : ℕ → ℝ := fun m =>
      (N / ((m : ℝ) + 1)) ^ 2 / N *
      (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        g ((i : ℝ) * (N / ((m : ℝ) + 1)) - (j : ℝ) * (N / ((m : ℝ) + 1)))).re
    have hR_nn : ∀ m : ℕ, 0 ≤ R m := fun m => riemannSum_nonneg_of_pd g hg_pd N hN m
    have hR_tendsto : Tendsto R atTop (𝓝 (∫ u in Set.Icc (-N) N,
        ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / N))).re) := by
      set F : ℝ → ℝ → ℝ := fun s t => (g (s - t)).re with hF_def
      have hF_cts : Continuous F.uncurry :=
        (Complex.continuous_re.comp hg_cont).comp (continuous_fst.sub continuous_snd)
      have hF_ucont : UniformContinuousOn F.uncurry
          (Set.Icc 0 N ×ˢ Set.Icc 0 N) :=
        (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
          hF_cts.continuousOn
      have hR_form : ∀ m : ℕ, R m = (1 / N) * (N / ((m : ℝ) + 1)) ^ 2 *
          (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            F ((i : ℝ) * (N / ((m : ℝ) + 1))) ((j : ℝ) * (N / ((m : ℝ) + 1)))) := by
        intro m
        simp only [R, F]
        rw [show (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            g (↑i * (N / (↑m + 1)) - ↑j * (N / (↑m + 1)))).re =
            ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            (g (↑i * (N / (↑m + 1)) - ↑j * (N / (↑m + 1)))).re from by
          simp [Complex.re_sum]]
        ring
      have htarget_eq : (∫ u in Set.Icc (-N) N,
          ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / N))).re =
          (1 / N) * ∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t :=
        tent_integral_eq_fubini g hg_cont N hN
      rw [htarget_eq]
      suffices hS : Tendsto (fun m : ℕ => (N / ((m : ℝ) + 1)) ^ 2 *
          ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            F ((i : ℝ) * (N / ((m : ℝ) + 1))) ((j : ℝ) * (N / ((m : ℝ) + 1))))
          atTop (𝓝 (∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t)) by
        have hR_eq : R = fun (m : ℕ) => (1 / N) * ((N / ((m : ℝ) + 1)) ^ 2 *
            ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
              F ((i : ℝ) * (N / ((m : ℝ) + 1))) ((j : ℝ) * (N / ((m : ℝ) + 1)))) :=
          funext (fun m => by rw [hR_form]; ring)
        rw [hR_eq]
        exact (tendsto_const_nhds (x := 1 / N)).mul hS
      exact tendsto_riemannSum_of_uniformContinuousOn F N hN hF_cts hF_ucont
    exact ge_of_tendsto hR_tendsto (Eventually.of_forall hR_nn)
private theorem tendsto_fejerApproximant (ψ : ℝ → ℂ) (hI : Integrable ψ volume) (x : ℝ) :
    Tendsto (fun n : ℕ => fejerApproximant ψ (↑n + 1) x)
      atTop (𝓝 (inverseFourierDensity ψ x)) := by
  unfold fejerApproximant inverseFourierDensity
  apply Filter.Tendsto.const_mul
  apply Complex.continuous_re.continuousAt.tendsto.comp
  set f : ℝ → ℂ := fun u => ψ u * exp (-(↑x * ↑u * I))
  set F : ℕ → ℝ → ℂ := fun n u =>
    (Set.Icc (-(↑n + 1 : ℝ)) (↑n + 1)).indicator
      (fun u => ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / (↑n + 1)))) u
  have hset_eq : ∀ n : ℕ, ∫ u in Set.Icc (-(↑n + 1 : ℝ)) (↑n + 1),
      ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / (↑n + 1))) =
      ∫ u, F n u := by
    intro n; rw [← integral_indicator (measurableSet_Icc)]
  simp_rw [hset_eq]
  apply tendsto_integral_of_dominated_convergence (fun u => ‖ψ u‖)
  ·
    intro n
    apply AEStronglyMeasurable.indicator _ measurableSet_Icc
    apply AEStronglyMeasurable.mul
    · exact (hI.1.mul ((((continuous_ofReal.comp continuous_const).mul continuous_ofReal).mul
        continuous_const).neg.cexp).aestronglyMeasurable)
    · exact (continuous_const.sub (continuous_ofReal.comp
        (continuous_abs.div_const _))).aestronglyMeasurable
  · exact hI.norm
  ·
    intro n; apply ae_of_all; intro u
    simp only [F]
    by_cases hu : u ∈ Set.Icc (-(↑n + 1 : ℝ)) (↑n + 1)
    · rw [Set.indicator_of_mem hu, norm_mul, norm_mul]
      have hN_pos : (0 : ℝ) < ↑n + 1 := by positivity
      have hu_abs_le : |u| ≤ ↑n + 1 :=
        abs_le.mpr ⟨by linarith [(Set.mem_Icc.mp hu).1], (Set.mem_Icc.mp hu).2⟩
      have hfrac_le : |u| / (↑n + 1) ≤ 1 := (div_le_one hN_pos).mpr hu_abs_le
      have hfrac_nn : 0 ≤ 1 - |u| / (↑n + 1) := by linarith
      calc ‖ψ u‖ * ‖exp (-(↑x * ↑u * I))‖ * ‖(1 - ↑(|u| / (↑n + 1)) : ℂ)‖
          ≤ ‖ψ u‖ * 1 * 1 := by
            gcongr
            · rw [show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
                norm_exp_ofReal_mul_I]
            ·
              calc ‖(1 : ℂ) - ↑(|u| / (↑n + 1))‖
                  = ‖(↑(1 - |u| / (↑n + 1)) : ℂ)‖ := by push_cast; ring_nf
                _ = |1 - |u| / (↑n + 1)| := Complex.norm_real _
                _ = 1 - |u| / (↑n + 1) := abs_of_nonneg hfrac_nn
                _ ≤ 1 := by linarith [div_nonneg (abs_nonneg u) (le_of_lt hN_pos)]
        _ = ‖ψ u‖ := by ring
    · rw [Set.indicator_apply, if_neg hu, norm_zero]; exact norm_nonneg _
  ·
    apply ae_of_all; intro u
    simp only [F]
    have hmem : ∀ᶠ n : ℕ in atTop, u ∈ Set.Icc (-(↑n + 1 : ℝ)) (↑n + 1) := by
      rw [Filter.eventually_atTop]
      exact ⟨⌈|u|⌉₊, fun n hn => by
        have hle : |u| ≤ ↑n + 1 := by
          calc |u| ≤ ↑⌈|u|⌉₊ := Nat.le_ceil |u|
            _ ≤ ↑n := Nat.cast_le.mpr hn
            _ ≤ ↑n + 1 := le_add_of_nonneg_right zero_le_one
        exact Set.mem_Icc.mpr ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩⟩
    have heq : ∀ᶠ n : ℕ in atTop,
        (Set.Icc (-(↑n + 1 : ℝ)) (↑n + 1)).indicator
          (fun u => ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / (↑n + 1)))) u =
        ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / (↑n + 1))) :=
      hmem.mono fun n hn => Set.indicator_of_mem hn _
    apply Tendsto.congr' (EventuallyEq.symm heq)
    have h_frac : Tendsto (fun n : ℕ => |u| / ((↑n : ℝ) + 1)) atTop (𝓝 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h_window : Tendsto (fun n : ℕ => (1 : ℂ) - ↑(|u| / ((↑n : ℝ) + 1))) atTop (𝓝 1) := by
      have hc : Tendsto (fun n : ℕ => (↑(|u| / ((↑n : ℝ) + 1)) : ℂ)) atTop (𝓝 0) := by
        rw [show (0 : ℂ) = ↑(0 : ℝ) from by simp]
        exact (Complex.continuous_ofReal.tendsto 0).comp h_frac
      have h1 : Tendsto (fun n : ℕ => (1 : ℂ) - ↑(|u| / ((↑n : ℝ) + 1))) atTop
          (𝓝 ((1 : ℂ) - 0)) := (tendsto_const_nhds (x := (1 : ℂ))).sub hc
      simp only [sub_zero] at h1
      exact h1
    conv_rhs => rw [show ψ u * exp (-(↑x * ↑u * I)) =
      ψ u * exp (-(↑x * ↑u * I)) * 1 from (mul_one _).symm]
    exact tendsto_const_nhds.mul h_window
private theorem inverseFourierDensity_nonneg (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (hI : Integrable ψ volume) (x : ℝ) : 0 ≤ inverseFourierDensity ψ x :=
  ge_of_tendsto (tendsto_fejerApproximant ψ hI x)
    (Eventually.of_forall fun n => fejerApproximant_nonneg ψ hψc hpd (↑n + 1) (by positivity) x)
private theorem continuous_inverseFourierDensity (ψ : ℝ → ℂ)
    (hψc : Continuous ψ) (hI : Integrable ψ volume) :
    Continuous (inverseFourierDensity ψ) := by
  unfold inverseFourierDensity
  apply Continuous.const_mul
  apply Complex.continuous_re.comp
  set G : ℝ → ℝ → ℂ := fun x u => ψ u * exp (-(↑x * ↑u * I)) with hG_def
  have hG_cont : Continuous fun x => ∫ u, G x u := by
    exact continuous_of_dominated
      (fun (x : ℝ) => by
        show AEStronglyMeasurable (fun u => ψ u * exp (-((x : ℂ) * ↑u * I))) volume
        exact (hψc.mul ((((continuous_ofReal.comp continuous_const).mul continuous_ofReal).mul
          continuous_const).neg.cexp)).aestronglyMeasurable)
      (fun x => ae_of_all _ fun u => by
        show ‖G x u‖ ≤ ‖ψ u‖
        simp only [G, norm_mul]
        rw [show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
          norm_exp_ofReal_mul_I, mul_one])
      hI.norm
      (ae_of_all _ fun u => by
        show Continuous fun (y : ℝ) => G y u
        simp only [G]
        refine Continuous.mul continuous_const (Complex.continuous_exp.comp ?_)
        exact ((Complex.continuous_ofReal.mul continuous_const).mul continuous_const).neg)
  convert hG_cont using 1
private theorem fourierTransform_rescaled_eq (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (hI : Integrable ψ volume) (y : ℝ) :
    𝓕 (fun w => ψ (2 * Real.pi * w)) y = ↑(inverseFourierDensity ψ y) := by
  have h2pi_ne : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  let g : ℝ → ℂ := fun u => Complex.exp (↑(-(u * y)) * Complex.I) * ψ u
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul]
  have heq_integrand : ∀ v : ℝ,
      Complex.exp (↑(-2 * Real.pi * v * y) * Complex.I) * ψ (2 * Real.pi * v) =
      g (2 * Real.pi * v) := by
    intro v; simp only [g]
    congr 1; congr 1; push_cast; ring
  simp_rw [heq_integrand]
  suffices h : |(2 * Real.pi)⁻¹| • ∫ u, g u = ↑(inverseFourierDensity ψ y) by
    calc ∫ v : ℝ, g (2 * Real.pi * v)
        = |(2 * Real.pi)⁻¹| • ∫ u, g u := Measure.integral_comp_mul_left g (2 * Real.pi)
      _ = ↑(inverseFourierDensity ψ y) := h
  rw [abs_inv, abs_of_pos h2pi_pos]
  have h_integral_im_zero : (∫ u, g u).im = 0 := by
    have h_conj_g : ∀ u : ℝ, conj (g u) = g (-u) := fun u => by
      simp only [g, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, conj_I, mul_neg]
      rw [← hpd.conj_neg u]
      congr 1
      congr 1; push_cast; ring
    have h_neg_subst : ∫ u : ℝ, g (-u) = ∫ u : ℝ, g u := by
      have hfun : (fun u : ℝ => g (-u)) = fun u => g ((-1) * u) := by ext; simp
      rw [hfun, Measure.integral_comp_mul_left g (-1)]
      norm_num
    have h_im_antisym : ∀ u : ℝ, Complex.im (g u) = -Complex.im (g (-u)) := fun u => by
      have heq := congr_arg Complex.im (h_conj_g u)
      simp only [conj_im] at heq
      linarith
    have hint : ∫ u : ℝ, Complex.im (g u) = 0 := by
      have heq1 : ∫ u : ℝ, Complex.im (g u) = ∫ u : ℝ, -Complex.im (g (-u)) := by
        congr 1; ext u; exact h_im_antisym u
      have heq2 : ∫ u : ℝ, Complex.im (g (-u)) = ∫ u : ℝ, Complex.im (g u) := by
        have hfun : (fun u : ℝ => Complex.im (g (-u))) =
            fun u => (Complex.im ∘ g) ((-1) * u) := by ext; simp [Function.comp]
        rw [hfun, Measure.integral_comp_mul_left (Complex.im ∘ g) (-1)]
        norm_num
      have heq3 := integral_neg (f := fun u : ℝ => Complex.im (g (-u))) (μ := volume)
      linarith
    have h_g_int_for_im : Integrable g volume := by
      apply Integrable.mono hI
      · show AEStronglyMeasurable (fun u : ℝ => Complex.exp (↑(-(u * y)) * I) * ψ u) volume
        exact ((Complex.continuous_exp.comp
          (((Complex.continuous_ofReal.comp
            ((continuous_id.mul continuous_const).neg)).mul
            continuous_const))).mul hψc).aestronglyMeasurable
      · apply ae_of_all; intro u
        show ‖Complex.exp (↑(-(u * y)) * I) * ψ u‖ ≤ ‖ψ u‖
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have h_im_eq : RCLike.im (∫ u : ℝ, g u) = 0 := by
      have key : ∫ u : ℝ, RCLike.im (g u) = RCLike.im (∫ u : ℝ, g u) :=
        integral_im h_g_int_for_im
      have hint' : (∫ u : ℝ, RCLike.im (g u)) = 0 := by exact_mod_cast hint
      linarith
    exact h_im_eq
  unfold inverseFourierDensity
  push_cast
  have h_eq_reorder : ∫ u : ℝ, ψ u * Complex.exp (-(↑y * ↑u * Complex.I)) =
      ∫ u : ℝ, g u := by
    congr 1; ext u; simp only [g]
    have hexpa : -(↑y * ↑u * Complex.I) = ↑(-(u * y)) * Complex.I := by push_cast; ring
    rw [hexpa, mul_comm]
  rw [h_eq_reorder]
  have h_int_re : (∫ u, g u) = ↑(∫ u, g u).re := by
    rw [Complex.ext_iff]; simp [h_integral_im_zero]
  rw [h_int_re]
  simp only [Complex.real_smul]
  push_cast [Complex.ofReal_re]
  rw [one_div]
set_option maxHeartbeats 800000 in
private theorem fubini_gaussianFourier_identity (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hI : Integrable ψ volume) (σ2 : ℝ) (hσ2 : 0 < σ2) :
    ∫ x : ℝ, (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))).re *
      Real.exp (-(x ^ 2 / (2 * σ2))) =
    Real.sqrt (2 * Real.pi * σ2) *
      (∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))).re := by
    have hstep1 : ∀ x : ℝ,
        (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))).re *
          Real.exp (-(x ^ 2 / (2 * σ2))) =
        ((∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2))))).re := by
      intro x
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    simp_rw [hstep1]
    have hψ_int_bdd : ∀ x : ℝ,
        ‖∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))‖ ≤ ∫ u, ‖ψ u‖ := by
      intro x
      calc ‖∫ u, ψ u * exp (-(↑x * ↑u * I))‖
          ≤ ∫ u, ‖ψ u * exp (-(↑x * ↑u * I))‖ := norm_integral_le_integral_norm _
        _ = ∫ u, ‖ψ u‖ := by
            congr 1; ext u; rw [norm_mul,
              show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
              norm_exp_ofReal_mul_I, mul_one]
    have hgauss_int : Integrable (fun x : ℝ =>
        Real.exp (-(x ^ 2 / (2 * σ2)))) volume := by
      have h := integrable_exp_neg_mul_sq (show 0 < 1 / (2 * σ2) by positivity)
      convert h using 1; ext x; congr 1; ring
    have hf_int : Integrable (fun x : ℝ =>
        (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) volume := by
      apply (hgauss_int.const_mul (∫ u, ‖ψ u‖)).mono'
      · apply AEStronglyMeasurable.mul
        ·
          have hcont_param : Continuous (fun x : ℝ =>
              ∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) := by
            set G : ℝ → ℝ → ℂ := fun x u => ψ u * exp (-(↑x * ↑u * I))
            exact continuous_of_dominated
              (fun (x : ℝ) => (hψc.mul ((((continuous_ofReal.comp continuous_const).mul
                continuous_ofReal).mul continuous_const).neg.cexp)).aestronglyMeasurable)
              (fun x => ae_of_all _ fun u => by
                show ‖G x u‖ ≤ ‖ψ u‖
                simp only [G, norm_mul]
                rw [show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
                  norm_exp_ofReal_mul_I, mul_one])
              hI.norm
              (ae_of_all _ fun u => by
                show Continuous fun (y : ℝ) => G y u
                simp only [G]
                refine Continuous.mul continuous_const (Complex.continuous_exp.comp ?_)
                exact ((Complex.continuous_ofReal.mul continuous_const).mul
                  continuous_const).neg)
          exact hcont_param.aestronglyMeasurable
        · exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
            (continuous_neg.comp ((continuous_pow 2).div_const _)))).aestronglyMeasurable
      · exact ae_of_all _ fun x => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.exp_nonneg _)]
          exact mul_le_mul_of_nonneg_right (hψ_int_bdd x) (Real.exp_nonneg _)
    conv_lhs =>
      arg 2; ext x
      rw [show ((∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2))))).re =
        Complex.re ((∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) from rfl]
    rw [show (fun x : ℝ => Complex.re ((∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2)))))) =
      (fun x : ℝ => RCLike.re ((∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2)))))) from rfl,
      integral_re hf_int]
    suffices hcomplex : (∫ x : ℝ, (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
        ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) =
      ↑(Real.sqrt (2 * Real.pi * σ2)) *
        ∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2))) by
      show (∫ x : ℝ, (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2))))).re =
        Real.sqrt (2 * Real.pi * σ2) *
          (∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))).re
      rw [hcomplex]
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    have hpull : ∀ x : ℝ,
        (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) * ↑(Real.exp (-(x ^ 2 / (2 * σ2)))) =
        ∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I)) * ↑(Real.exp (-(x ^ 2 / (2 * σ2)))) := by
      intro x; exact (integral_mul_const _ _).symm
    simp_rw [hpull]
    have hcont_prod : Continuous (fun p : ℝ × ℝ =>
        ψ p.2 * exp (-(↑p.1 * ↑p.2 * I)) *
          ↑(Real.exp (-(p.1 ^ 2 / (2 * σ2))))) :=
      ((hψc.comp continuous_snd).mul
        (Complex.continuous_exp.comp
          (((continuous_ofReal.comp continuous_fst).mul
            (continuous_ofReal.comp continuous_snd)).mul
            continuous_const).neg)).mul
        (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
          (continuous_neg.comp ((continuous_pow 2 |>.comp continuous_fst).div_const _))))
    have hprod_int : Integrable (fun p : ℝ × ℝ =>
        ψ p.2 * exp (-(↑p.1 * ↑p.2 * I)) *
          ↑(Real.exp (-(p.1 ^ 2 / (2 * σ2))))) (volume.prod volume) := by
      rw [integrable_prod_iff hcont_prod.aestronglyMeasurable]
      refine ⟨?_, ?_⟩
      · exact ae_of_all _ fun x => by
          show Integrable (fun u => ψ u * exp (-(↑x * ↑u * I)) *
            ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) volume
          apply Integrable.mono' (hI.norm.mul_const (Real.exp (-(x ^ 2 / (2 * σ2)))))
          · exact (hcont_prod.comp
              (continuous_const.prodMk continuous_id)).aestronglyMeasurable
          · exact ae_of_all _ fun u => by
              rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (Real.exp_nonneg _),
                show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
                norm_exp_ofReal_mul_I, mul_one]
      · have hnorm_eq : (fun x => ∫ u, ‖(fun p : ℝ × ℝ => ψ p.2 *
            exp (-(↑p.1 * ↑p.2 * I)) *
              ↑(Real.exp (-(p.1 ^ 2 / (2 * σ2))))) (x, u)‖) =
            fun x => (∫ u, ‖ψ u‖) * Real.exp (-(x ^ 2 / (2 * σ2))) := by
          ext x
          show ∫ u, ‖ψ u * exp (-(↑x * ↑u * I)) *
            ↑(Real.exp (-(x ^ 2 / (2 * σ2))))‖ =
            (∫ u, ‖ψ u‖) * Real.exp (-(x ^ 2 / (2 * σ2)))
          simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.exp_nonneg _)]
          rw [← integral_mul_const]
          congr 1; ext u
          rw [show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
            norm_exp_ofReal_mul_I, mul_one]
        rw [hnorm_eq]
        exact hgauss_int.const_mul _
    rw [integral_integral_swap hprod_int]
    have hinner_eq : ∀ u : ℝ,
        (∫ x : ℝ, ψ u * exp (-(↑x * ↑u * I)) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) =
        ψ u * (↑(Real.sqrt (2 * Real.pi * σ2)) *
          ↑(Real.exp (-(σ2 * u ^ 2 / 2)))) := by
      intro u
      have hassoc : ∀ x : ℝ, ψ u * exp (-(↑x * ↑u * I)) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2)))) =
        ψ u * (exp (-(↑x * ↑u * I)) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) := fun x => by ring
      simp_rw [hassoc]
      rw [show (∫ x : ℝ, ψ u * (exp (-(↑x * ↑u * I)) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2)))))) =
        ψ u * ∫ x : ℝ, exp (-(↑x * ↑u * I)) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2))))
        from integral_const_mul _ _]
      congr 1
      have hrw : ∀ x : ℝ,
          exp (-(↑x * ↑u * I)) * ↑(Real.exp (-(x ^ 2 / (2 * σ2)))) =
          cexp (I * (-↑u) * ↑x) *
            cexp (-(↑(1 / (2 * σ2)) : ℂ) * (↑x) ^ 2) := by
        intro x
        congr 1
        · congr 1; ring
        · rw [Complex.ofReal_exp]; congr 1; push_cast; ring
      simp_rw [hrw]
      have hb_re : (0 : ℝ) < (↑(1 / (2 * σ2)) : ℂ).re := by
        simp [Complex.ofReal_re]; positivity
      rw [fourierIntegral_gaussian hb_re (-↑u)]
      have h1 : (↑(1 / (2 * σ2)) : ℂ) = 1 / (2 * ↑σ2) := by push_cast; ring
      rw [h1]
      have h2piσ_nn : (0 : ℝ) ≤ 2 * Real.pi * σ2 := by positivity
      have hbase : (↑Real.pi : ℂ) / (1 / (2 * ↑σ2)) = ↑(2 * Real.pi * σ2) := by
        push_cast; field_simp
      rw [hbase, show (1 / 2 : ℂ) = ↑(1 / 2 : ℝ) from by push_cast; ring,
        ← ofReal_cpow h2piσ_nn,
        show (2 * Real.pi * σ2) ^ (1 / 2 : ℝ) = Real.sqrt (2 * Real.pi * σ2) from
          (Real.sqrt_eq_rpow _).symm]
      congr 1
      rw [Complex.ofReal_exp]; congr 1
      push_cast
      have hσ2_ne : (↑σ2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hσ2)
      field_simp; ring
    simp_rw [hinner_eq]
    simp_rw [show ∀ u : ℝ, ψ u * (↑(Real.sqrt (2 * Real.pi * σ2)) *
        ↑(Real.exp (-(σ2 * u ^ 2 / 2)))) =
      ↑(Real.sqrt (2 * Real.pi * σ2)) * (ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2))))
      from fun u => by ring]
    exact integral_const_mul _ _
set_option maxHeartbeats 800000 in
private theorem gaussianSmoothed_lintegral_le_one (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (h0 : ψ 0 = 1)
    (hI : Integrable ψ volume) (σ2 : ℝ) (hσ2 : 0 < σ2)
    (hρ_nn : ∀ x, 0 ≤ inverseFourierDensity ψ x) :
    ∫⁻ x, ENNReal.ofReal (inverseFourierDensity ψ x *
      Real.exp (-(x ^ 2 / (2 * σ2)))) ∂volume ≤ 1 := by
  have hρ_cont := continuous_inverseFourierDensity ψ hψc hI
  have hgn_nn : ∀ x, 0 ≤ inverseFourierDensity ψ x *
      Real.exp (-(x ^ 2 / (2 * σ2))) :=
    fun x => mul_nonneg (hρ_nn x) (Real.exp_nonneg _)
  have hρ_bdd : ∃ C, ∀ x, inverseFourierDensity ψ x ≤ C := by
    use (1 / (2 * Real.pi)) * ∫ u, ‖ψ u‖
    intro x
    unfold inverseFourierDensity
    apply mul_le_mul_of_nonneg_left _ (div_nonneg one_pos.le
      (mul_pos (by norm_num : (0:ℝ) < 2) Real.pi_pos).le)
    calc (∫ u, ψ u * exp (-(↑x * ↑u * I))).re
        ≤ |(∫ u, ψ u * exp (-(↑x * ↑u * I))).re| := le_abs_self _
      _ ≤ ‖∫ u, ψ u * exp (-(↑x * ↑u * I))‖ := abs_re_le_norm _
      _ ≤ ∫ u, ‖ψ u * exp (-(↑x * ↑u * I))‖ := norm_integral_le_integral_norm _
      _ = ∫ u, ‖ψ u‖ := by
          congr 1; ext u; rw [norm_mul,
            show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
            norm_exp_ofReal_mul_I, mul_one]
  have hgn_integrable : Integrable (fun x => inverseFourierDensity ψ x *
      Real.exp (-(x ^ 2 / (2 * σ2)))) volume := by
    have hgauss_cont : Continuous (fun x : ℝ =>
        Real.exp (-(x ^ 2 / (2 * σ2)))) :=
      Real.continuous_exp.comp (continuous_neg.comp
        ((continuous_pow 2).div_const _))
    have hgauss_int : Integrable (fun x : ℝ =>
        Real.exp (-(x ^ 2 / (2 * σ2)))) volume := by
      have h := integrable_exp_neg_mul_sq (show 0 < 1 / (2 * σ2) by positivity)
      convert h using 1; ext x; congr 1; ring
    obtain ⟨C, hC⟩ := hρ_bdd
    exact hgauss_int.bdd_mul hρ_cont.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hρ_nn x)]; exact hC x)
  rw [← ofReal_integral_eq_lintegral_ofReal hgn_integrable (ae_of_all _ hgn_nn)]
  rw [ENNReal.ofReal_le_one]
  have hψ_norm_le : ∀ u, ‖ψ u‖ ≤ 1 := hpd.norm_le_one h0
  have gaussian_fubini_bound :
      ∫ x, inverseFourierDensity ψ x * Real.exp (-(x ^ 2 / (2 * σ2))) ≤
      Real.sqrt σ2 / Real.sqrt (2 * Real.pi) *
      ∫ u, ‖ψ u‖ * Real.exp (-(σ2 * u ^ 2 / 2)) := by
    have fubini_identity := fubini_gaussianFourier_identity ψ hψc hI σ2 hσ2
    have hpi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    have hLHS_eq : ∫ x, inverseFourierDensity ψ x *
        Real.exp (-(x ^ 2 / (2 * σ2))) =
      1 / (2 * Real.pi) * (∫ x : ℝ, (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))).re *
        Real.exp (-(x ^ 2 / (2 * σ2)))) := by
      simp_rw [inverseFourierDensity, mul_assoc]
      rw [integral_const_mul]
    rw [hLHS_eq, fubini_identity]
    have hRe_le : (∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))).re ≤
        ∫ u : ℝ, ‖ψ u‖ * Real.exp (-(σ2 * u ^ 2 / 2)) := by
      calc (∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))).re
          ≤ ‖∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))‖ :=
            le_trans (le_abs_self _) (abs_re_le_norm _)
        _ ≤ ∫ u : ℝ, ‖ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ u : ℝ, ‖ψ u‖ * Real.exp (-(σ2 * u ^ 2 / 2)) := by
            congr 1; ext u
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Real.exp_nonneg _)]
    set I_re := (∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))).re
    set I_norm := ∫ u : ℝ, ‖ψ u‖ * Real.exp (-(σ2 * u ^ 2 / 2))
    have hI_norm_nn : 0 ≤ I_norm :=
      integral_nonneg fun u => mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)
    have hI_re_le_norm : I_re ≤ I_norm := hRe_le
    have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr hpi_pos
    have hsqrt_nn : 0 ≤ Real.sqrt σ2 := Real.sqrt_nonneg _
    have hc_eq : 1 / (2 * Real.pi) * Real.sqrt (2 * Real.pi * σ2) =
        Real.sqrt σ2 / Real.sqrt (2 * Real.pi) := by
      rw [show (2 * Real.pi * σ2) = (2 * Real.pi) * σ2 from by ring,
        Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
      have h := ne_of_gt hsqrt_pos
      field_simp
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
    have h1 : 1 / (2 * Real.pi) * (Real.sqrt (2 * Real.pi * σ2) * I_re)
      = Real.sqrt σ2 / Real.sqrt (2 * Real.pi) * I_re := by
      rw [← hc_eq]; ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left hI_re_le_norm
      (div_nonneg hsqrt_nn hsqrt_pos.le)
  calc ∫ x, inverseFourierDensity ψ x * Real.exp (-(x ^ 2 / (2 * σ2)))
      ≤ Real.sqrt σ2 / Real.sqrt (2 * Real.pi) *
        ∫ u, ‖ψ u‖ * Real.exp (-(σ2 * u ^ 2 / 2)) := gaussian_fubini_bound
    _ ≤ Real.sqrt σ2 / Real.sqrt (2 * Real.pi) *
        ∫ u, Real.exp (-(σ2 * u ^ 2 / 2)) := by
        have hexp_int : Integrable (fun u : ℝ =>
            Real.exp (-(σ2 * u ^ 2 / 2))) volume := by
          apply (integrable_exp_neg_mul_sq (by positivity : 0 < σ2 / 2)).mono'
            (by fun_prop)
          exact ae_of_all _ fun u => by
            rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
            apply Real.exp_le_exp_of_le; linarith [sq_nonneg u]
        apply mul_le_mul_of_nonneg_left
        · apply integral_mono_of_nonneg
          · exact ae_of_all _ fun u => mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)
          · exact hexp_int
          · exact ae_of_all _ fun u =>
              mul_le_of_le_one_left (Real.exp_nonneg _) (hψ_norm_le u)
        · exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = 1 := by
        have h_int_eq : (∫ u : ℝ, Real.exp (-(σ2 * u ^ 2 / 2))) =
            Real.sqrt (2 * Real.pi / σ2) := by
          have h1 := integral_gaussian (σ2 / 2)
          calc (∫ u : ℝ, Real.exp (-(σ2 * u ^ 2 / 2)))
              = ∫ u : ℝ, Real.exp (-(σ2 / 2) * u ^ 2) := by
                congr 1; ext u; congr 1; ring
            _ = Real.sqrt (Real.pi / (σ2 / 2)) := h1
            _ = Real.sqrt (2 * Real.pi / σ2) := by
                congr 1; field_simp
        rw [h_int_eq, Real.sqrt_div (by positivity : (0:ℝ) ≤ 2 * Real.pi),
          div_mul_div_comm, mul_comm (Real.sqrt σ2) (Real.sqrt (2 * Real.pi)),
          div_self (ne_of_gt (mul_pos (Real.sqrt_pos.mpr
            (by positivity : 0 < 2 * Real.pi)) (Real.sqrt_pos.mpr hσ2)))]
set_option maxHeartbeats 800000 in
private theorem integrable_inverseFourierDensity (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (h0 : ψ 0 = 1) (hI : Integrable ψ volume) :
    Integrable (inverseFourierDensity ψ) volume := by
  have hρ_nn := inverseFourierDensity_nonneg ψ hψc hpd hI
  have hρ_cont := continuous_inverseFourierDensity ψ hψc hI
  have hρ_meas : AEStronglyMeasurable (inverseFourierDensity ψ) volume :=
    hρ_cont.aestronglyMeasurable
  apply (lintegral_ofReal_ne_top_iff_integrable hρ_meas (ae_of_all _ hρ_nn)).mp
  set gn : ℕ → ℝ → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal (inverseFourierDensity ψ x * Real.exp (-(x ^ 2 / (2 * (↑n + 1)))))
  have hgn_mono : ∀ᵐ x ∂volume, Monotone (fun n => gn n x) := by
    apply ae_of_all; intro x m n hmn
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left
    · apply Real.exp_le_exp_of_le
      apply neg_le_neg
      apply div_le_div_of_nonneg_left (sq_nonneg x)
      · linarith [show (0 : ℝ) ≤ ↑n from Nat.cast_nonneg n]
      · linarith [show (0 : ℝ) ≤ ↑m from Nat.cast_nonneg m,
                   show (↑m : ℝ) ≤ ↑n from Nat.cast_le.mpr hmn]
    · exact hρ_nn x
  have hgn_tendsto : ∀ᵐ x ∂volume, Tendsto (fun n => gn n x) atTop
      (𝓝 (ENNReal.ofReal (inverseFourierDensity ψ x))) := by
    apply ae_of_all; intro x
    apply ENNReal.tendsto_ofReal
    conv_rhs => rw [show inverseFourierDensity ψ x =
      inverseFourierDensity ψ x * 1 from (mul_one _).symm]
    apply Tendsto.mul tendsto_const_nhds
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact (Real.continuous_exp.tendsto 0).comp (by
      have : Tendsto (fun n : ℕ => x ^ 2 / (2 * (↑n + 1))) atTop (𝓝 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds
          ((Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_mul_atTop
            (by norm_num : (0 : ℝ) < 2))
      simpa using this.neg)
  have hgn_meas : ∀ n, AEMeasurable (gn n) volume := by
    intro n
    exact (hρ_cont.mul (Real.continuous_exp.comp (continuous_neg.comp
      ((continuous_pow 2).div_const _)))).measurable.ennreal_ofReal.aemeasurable
  have hMCT := lintegral_tendsto_of_tendsto_of_monotone hgn_meas hgn_mono hgn_tendsto
  have hgn_le_one : ∀ n, ∫⁻ x, gn n x ∂volume ≤ 1 := by
    intro n
    set σ2 : ℝ := ↑n + 1 with hσ2_def
    have hσ2_pos : 0 < σ2 := by positivity
    rw [show gn n = fun x => ENNReal.ofReal (inverseFourierDensity ψ x *
        Real.exp (-(x ^ 2 / (2 * σ2)))) from by ext x; simp [gn, hσ2_def]]
    exact gaussianSmoothed_lintegral_le_one ψ hψc hpd h0 hI σ2 hσ2_pos hρ_nn
  have hbdd : ∫⁻ x, ENNReal.ofReal (inverseFourierDensity ψ x) ∂volume ≤ 1 :=
    le_of_tendsto' hMCT hgn_le_one
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hbdd
set_option maxHeartbeats 800000 in
private theorem charFun_inverseFourierDensity (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (h0 : ψ 0 = 1) (hI : Integrable ψ volume) (ξ : ℝ) :
    ∫ x, (inverseFourierDensity ψ x : ℝ) • exp (↑ξ * ↑x * I) = ψ ξ := by
  have h2pi_ne : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  set f : ℝ → ℂ := fun w => ψ (2 * Real.pi * w) with hf_def
  have hf_int : Integrable f volume := by
    show Integrable (fun w => ψ (2 * Real.pi * w)) volume
    exact hI.comp_mul_left' h2pi_ne
  have hf_cont : Continuous f := hψc.comp (continuous_const.mul continuous_id)
  have hFf_eq : ∀ y, 𝓕 f y = ↑(inverseFourierDensity ψ y) :=
    fourierTransform_rescaled_eq ψ hψc hpd hI
  have hFf_int : Integrable (𝓕 f) volume := by
    rw [show 𝓕 f = fun y => (↑(inverseFourierDensity ψ y) : ℂ) from funext hFf_eq]
    exact (integrable_inverseFourierDensity ψ hψc hpd h0 hI).ofReal
  have hinv := hf_cont.fourierInv_fourier_eq hf_int hFf_int
  set v := ξ / (2 * Real.pi) with hv_def
  have hfv : f v = ψ ξ := by
    simp only [hf_def, hv_def, mul_div_cancel₀ _ h2pi_ne]
  have hinv_v := congr_fun hinv v
  rw [hfv] at hinv_v
  rw [← hinv_v]
  rw [Real.fourierInv_eq']
  simp_rw [hFf_eq]
  congr 1; ext y
  simp only [Complex.real_smul, hv_def, Complex.ofReal_mul]
  rw [mul_comm]
  congr 1
  congr 1
  have hInner : ⟪y, ξ / (2 * Real.pi)⟫ = ξ / (2 * Real.pi) * y := by
    rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial]
    exact AddMonoidHom.id_apply (M := ℝ) _
  have hCast : (↑⟪y, ξ / (2 * Real.pi)⟫ : ℂ) = ↑ξ / ↑(2 * Real.pi) * ↑y := by
    push_cast [hInner]; ring
  rw [hCast]
  push_cast
  field_simp [Real.pi_ne_zero]
private theorem integral_inverseFourierDensity_eq_one (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (h0 : ψ 0 = 1) (hI : Integrable ψ volume) :
    ∫ x, inverseFourierDensity ψ x = 1 := by
  have h := charFun_inverseFourierDensity ψ hψc hpd h0 hI 0
  have heq : ∀ x : ℝ, (inverseFourierDensity ψ x : ℝ) • exp ((0 : ℝ) * ↑x * I) =
      ↑(inverseFourierDensity ψ x) := by
    intro x; simp [Complex.real_smul]
  simp_rw [heq, h0] at h
  have := congr_arg Complex.re h
  simp only [Complex.one_re] at this
  rwa [show (∫ x : ℝ, (↑(inverseFourierDensity ψ x) : ℂ)).re =
    ∫ x, inverseFourierDensity ψ x from by
    have : ∫ x : ℝ, (↑(inverseFourierDensity ψ x) : ℂ) =
      ↑(∫ x, inverseFourierDensity ψ x) := integral_ofReal
    rw [this, Complex.ofReal_re]] at this
private theorem exists_probMeasure_of_pd_integrable
    (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hpd : IsPositiveDefinite ψ)
    (h0 : ψ 0 = 1) (_hI : Integrable ψ volume) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ ξ, ProbabilityMeasure.characteristicFun μ ξ = ψ ξ := by
  set ρ := inverseFourierDensity ψ with hρ_def
  have hρ_nn : ∀ x, 0 ≤ ρ x := inverseFourierDensity_nonneg ψ hψc hpd _hI
  have hρ_cont := continuous_inverseFourierDensity ψ hψc _hI
  have hρ_int : ∫ x, ρ x = 1 := integral_inverseFourierDensity_eq_one ψ hψc hpd h0 _hI
  have hρ_integrable : Integrable ρ volume := integrable_of_integral_eq_one hρ_int
  set μ_raw : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x)) with hμ_def
  have hμ_prob : IsProbabilityMeasure μ_raw := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ]
    rw [Measure.restrict_univ]
    rw [show (∫⁻ x, ENNReal.ofReal (ρ x)) = ENNReal.ofReal (∫ x, ρ x) from by
      rw [ofReal_integral_eq_lintegral_ofReal hρ_integrable (ae_of_all _ hρ_nn)]]
    rw [hρ_int, ENNReal.ofReal_one]
  set μ_pm : ProbabilityMeasure ℝ := ⟨μ_raw, hμ_prob⟩ with hμ_pm_def
  refine ⟨μ_pm, fun ξ => ?_⟩
  simp only [MeasureTheory.ProbabilityMeasure.characteristicFun_def, charFun_apply_real]
  change ∫ x, exp (↑ξ * ↑x * I) ∂μ_raw = ψ ξ
  rw [hμ_def, integral_withDensity_eq_integral_toReal_smul
    (hρ_cont.measurable.ennreal_ofReal)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have h_eq : ∀ x : ℝ, (ENNReal.ofReal (inverseFourierDensity ψ x)).toReal =
      inverseFourierDensity ψ x := fun x => ENNReal.toReal_ofReal (hρ_nn x)
  simp_rw [h_eq]
  exact charFun_inverseFourierDensity ψ hψc hpd h0 _hI ξ
private theorem isTight_of_charFun_pointwise_tendsto
    {μs : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (_hφc : Continuous φ) (_hφ0 : φ 0 = 1)
    (_hconv : ∀ ξ, Tendsto (fun n => charFun (μs n : Measure ℝ) ξ) atTop (𝓝 (φ ξ))) :
    IsTightMeasureSet (range (fun n => (μs n : Measure ℝ))) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hε_top : ε = ⊤
  · exact ⟨∅, isCompact_empty, fun _ _ => hε_top ▸ le_top⟩
  set δ := ε.toReal with hδ_def
  have hδ_pos : 0 < δ := ENNReal.toReal_pos hε.ne' hε_top
  have hδ_le : ENNReal.ofReal δ ≤ ε := by
    rw [hδ_def, ENNReal.ofReal_toReal hε_top]
  obtain ⟨r, hr, n₀, htail⟩ :=
    MeasureTheory.ProbabilityMeasure.exists_radius_and_threshold_of_continuous_tendsto _hφc _hφ0 _hconv hδ_pos
  have hfin : ∀ n : Fin n₀, ∃ K : Set ℝ, IsCompact K ∧ (μs n : Measure ℝ) Kᶜ ≤ ε := by
    intro ⟨n, hn⟩
    have := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (isTightMeasureSet_singleton (μ := (μs n : Measure ℝ))) ε hε
    obtain ⟨K, hK, hKε⟩ := this
    exact ⟨K, hK, hKε _ rfl⟩
  choose Kfin hKfin_compact hKfin_meas using hfin
  refine ⟨(⋃ i : Fin n₀, Kfin i) ∪ Metric.closedBall 0 r,
    (isCompact_iUnion fun i => hKfin_compact i).union (isCompact_closedBall 0 r), ?_⟩
  intro ν hν
  obtain ⟨n, rfl⟩ := hν
  by_cases hn : n < n₀
  · calc (μs n : Measure ℝ) ((⋃ i : Fin n₀, Kfin i) ∪ Metric.closedBall 0 r)ᶜ
        ≤ (μs n : Measure ℝ) (Kfin ⟨n, hn⟩)ᶜ := by
          apply measure_mono
          apply compl_subset_compl.mpr
          exact subset_union_of_subset_left (subset_iUnion Kfin ⟨n, hn⟩) _
      _ ≤ ε := hKfin_meas ⟨n, hn⟩
  · push Not at hn
    have hcompl_sub : ((⋃ i : Fin n₀, Kfin i) ∪ Metric.closedBall 0 r)ᶜ ⊆
        (Metric.closedBall (0 : ℝ) r)ᶜ :=
      compl_subset_compl.mpr subset_union_right
    have hball_eq : (Metric.closedBall (0 : ℝ) r)ᶜ = {x | r < |x|} := by
      ext x
      simp only [mem_compl_iff, Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le,
        mem_setOf_eq, lt_abs]
    calc (μs n : Measure ℝ) ((⋃ i : Fin n₀, Kfin i) ∪ Metric.closedBall 0 r)ᶜ
        ≤ (μs n : Measure ℝ) (Metric.closedBall 0 r)ᶜ := measure_mono hcompl_sub
      _ = (μs n : Measure ℝ) {x | r < |x|} := by rw [hball_eq]
      _ = ENNReal.ofReal ((μs n : Measure ℝ).real {x | r < |x|}) := by
          rw [ofReal_measureReal]
      _ ≤ ENNReal.ofReal δ := by
          exact ENNReal.ofReal_le_ofReal (le_of_lt (htail n hn))
      _ ≤ ε := hδ_le
section GaussianSmoothing
private noncomputable def gaussianVar (n : ℕ) : ℝ≥0 := ⟨1 / (↑n + 1), by positivity⟩
private noncomputable def gaussianPM (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 (gaussianVar n), inferInstance⟩
private theorem pd_gaussianCharFun (n : ℕ) :
    IsPositiveDefinite (fun ξ => charFun (gaussianReal 0 (gaussianVar n)) ξ) := by
  show IsPositiveDefinite (fun ξ => charFun (gaussianPM n : Measure ℝ) ξ)
  exact IsPositiveDefinite.of_charFun (gaussianPM n)
private theorem pd_smoothed {φ : ℝ → ℂ} (hpd : IsPositiveDefinite φ) (n : ℕ) :
    IsPositiveDefinite (fun ξ => φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ) :=
  hpd.mul (pd_gaussianCharFun n)
private theorem smoothed_at_zero {φ : ℝ → ℂ} (h0 : φ 0 = 1) (n : ℕ) :
    φ 0 * charFun (gaussianReal 0 (gaussianVar n)) 0 = 1 := by
  simp [h0, charFun_zero]
private theorem continuous_charFun_gaussianVar (n : ℕ) :
    Continuous (fun ξ => charFun (gaussianReal 0 (gaussianVar n)) ξ) := by
  simp_rw [charFun_gaussianReal]
  fun_prop
private theorem continuous_smoothed {φ : ℝ → ℂ} (hφc : Continuous φ) (n : ℕ) :
    Continuous (fun ξ => φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ) :=
  hφc.mul (continuous_charFun_gaussianVar n)
private theorem integrable_charFun_gaussianVar (n : ℕ) :
    Integrable (fun ξ => charFun (gaussianReal 0 (gaussianVar n)) ξ) volume := by
  set v := gaussianVar n
  have hv_pos : (0 : ℝ) < (v : ℝ≥0) := by
    have hval : ((v : ℝ≥0) : ℝ) = 1 / (↑n + 1) := rfl
    rw [hval]; positivity
  have hnorm_eq : ∀ ξ : ℝ, ‖charFun (gaussianReal 0 v) ξ‖ = Real.exp (-((v : ℝ) / 2 * ξ ^ 2)) := by
    intro ξ
    rw [charFun_gaussianReal, Complex.norm_exp]
    congr 1
    simp only [ofReal_zero, mul_zero, zero_mul, zero_sub,
      Complex.neg_re, Complex.div_ofNat_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    rw [show ((↑ξ : ℂ) ^ 2).re = ξ ^ 2 by
      simp only [sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]]
    ring
  refine (integrable_exp_neg_mul_sq (by linarith : 0 < (v : ℝ) / 2)).mono'
    (continuous_charFun_gaussianVar n).aestronglyMeasurable ?_
  exact ae_of_all _ fun ξ => by
    rw [hnorm_eq]
    exact Real.exp_le_exp_of_le (by nlinarith)
private theorem integrable_smoothed {φ : ℝ → ℂ} (hφc : Continuous φ)
    (hpd : IsPositiveDefinite φ) (h0 : φ 0 = 1) (n : ℕ) :
    Integrable (fun ξ => φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ) volume := by
  exact (integrable_charFun_gaussianVar n).mono
    (continuous_smoothed hφc n).aestronglyMeasurable
    (ae_of_all _ fun ξ => by
      rw [norm_mul]
      calc ‖φ ξ‖ * ‖charFun (gaussianReal 0 (gaussianVar n)) ξ‖
          ≤ 1 * ‖charFun (gaussianReal 0 (gaussianVar n)) ξ‖ :=
            mul_le_mul_of_nonneg_right (hpd.norm_le_one h0 ξ) (norm_nonneg _)
        _ = ‖charFun (gaussianReal 0 (gaussianVar n)) ξ‖ := one_mul _)
private theorem tendsto_gaussianCharFun_one (ξ : ℝ) :
    Tendsto (fun n => charFun (gaussianReal 0 (gaussianVar n)) ξ) atTop (𝓝 1) := by
  simp_rw [charFun_gaussianReal]
  simp only [ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [show (1 : ℂ) = cexp 0 from by simp]
  apply Filter.Tendsto.cexp
  rw [show (0 : ℂ) = -(0 * (↑ξ : ℂ) ^ 2 / 2) from by simp]
  have hv_tendsto : Tendsto (fun n : ℕ => (↑↑(gaussianVar n) : ℂ)) atTop (𝓝 0) := by
    rw [show (0 : ℂ) = ↑(0 : ℝ) from by simp]
    exact (Complex.continuous_ofReal.tendsto 0).comp (by
      show Tendsto (fun n : ℕ => (↑(gaussianVar n) : ℝ)) atTop (𝓝 0)
      simp only [gaussianVar]
      exact tendsto_one_div_add_atTop_nhds_zero_nat)
  exact (((hv_tendsto.mul tendsto_const_nhds).div_const _).neg)
private theorem tendsto_smoothed (φ : ℝ → ℂ) (ξ : ℝ) :
    Tendsto (fun n => φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ) atTop (𝓝 (φ ξ)) := by
  conv_rhs => rw [show φ ξ = φ ξ * 1 from (mul_one _).symm]
  exact tendsto_const_nhds.mul (tendsto_gaussianCharFun_one ξ)
end GaussianSmoothing
theorem bochner
    (φ : ℝ → ℂ) (hφc : Continuous φ) (hpd : IsPositiveDefinite φ)
    (h0 : φ 0 = 1) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ ξ, MeasureTheory.ProbabilityMeasure.characteristicFun μ ξ = φ ξ := by
  have hsmoothed : ∀ n : ℕ, ∃ μn : ProbabilityMeasure ℝ,
      ∀ ξ, ProbabilityMeasure.characteristicFun μn ξ =
        φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ :=
    fun n => exists_probMeasure_of_pd_integrable _ (continuous_smoothed hφc n)
      (pd_smoothed hpd n) (smoothed_at_zero h0 n) (integrable_smoothed hφc hpd h0 n)
  choose μs hμs using hsmoothed
  have hcharfun_conv :
      ∀ ξ, Tendsto (fun n => charFun (μs n : Measure ℝ) ξ) atTop (𝓝 (φ ξ)) := by
    intro ξ
    have : ∀ n, charFun (μs n : Measure ℝ) ξ =
        φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ := by
      intro n; exact (hμs n ξ).symm ▸ rfl
    simp_rw [this]
    exact tendsto_smoothed φ ξ
  have htight := isTight_of_charFun_pointwise_tendsto hφc h0 hcharfun_conv
  have htight' : IsTightMeasureSet
      {((ν : ProbabilityMeasure ℝ) : Measure ℝ) | ν ∈ range μs} := by
    convert htight using 1
    ext x; simp [mem_range]
  have hcompact : IsCompact (closure (range μs)) :=
    isCompact_closure_of_isTightMeasureSet htight'
  have hin_closure : ∀ n, μs n ∈ closure (range μs) :=
    fun n => subset_closure (mem_range_self n)
  obtain ⟨ν, _, ns, hns_mono, hns_tendsto⟩ := hcompact.tendsto_subseq hin_closure
  have hcharfun_ν : ∀ ξ, ProbabilityMeasure.characteristicFun ν ξ = φ ξ := by
    intro ξ
    have h_weak := ProbabilityMeasure.charFunTendsto_of_tendsto hns_tendsto ξ
    simp only [Function.comp_def, ProbabilityMeasure.characteristicFun_def] at h_weak
    have h_phi := (hcharfun_conv ξ).comp hns_mono.tendsto_atTop
    exact (ProbabilityMeasure.characteristicFun_def ν ξ).symm ▸
      tendsto_nhds_unique h_weak h_phi
  exact ⟨ν, hcharfun_ν⟩
end ProbabilityTheory


