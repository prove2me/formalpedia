-- Prove2me | solution 1 for Arxiv2105_07250.doubly_averaged_retrieval
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T08:54:48.192839+00:00
-- url     : https://prove2.me/submissions/5d0e475d-43d9-4262-9850-a43faf9e1ae7

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section
namespace DA
open Arxiv2105_07250

lemma recprod (G1 G2 : ℝ → ℂ) (S : Set ℝ) :
    starRingEnd ℂ (∫ x', S.indicator G1 x') * ∫ x'', S.indicator G2 x'' =
      ∫ p : ℝ × ℝ, ((S.indicator (fun _ => (1:ℝ)) p.1 * S.indicator (fun _ => (1:ℝ)) p.2 : ℝ) : ℂ) *
        (starRingEnd ℂ (G1 p.1) * G2 p.2) ∂(volume.prod volume) := by
  rw [← integral_conj, ← integral_prod_mul]
  congr 1; funext p
  by_cases h1 : p.1 ∈ S <;> by_cases h2 : p.2 ∈ S <;> simp [Set.indicator, h1, h2]

end DA

open Arxiv2105_07250 DA in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c) (F : Ω → ℝ → ℂ)
    (hF : Measurable (Function.uncurry F)) (GA GB : ℝ → ℂ) (hGA : Measurable GA)
    (hGB : Measurable GB)
    (hfub : Integrable (fun q : Ω × ℝ × ℝ =>
      starRingEnd ℂ (F q.1 q.2.1 * GA q.2.1) * (F q.1 q.2.2 * GB q.2.2))
      (P.prod (volume.prod volume)))
    (vabs T : ℝ) (hv : 0 < vabs) (hT : 0 < T) (fT : ℝ → ℝ) (hf : IsWindowDensity fT) :
    (∀ x' x'' : ℝ, windowKernel fT vabs T x' x'' = windowKernel fT vabs T x'' x') ∧
    (∀ x' x'' : ℝ, 2 * T * vabs < |x' - x''| → windowKernel fT vabs T x' x'' = 0) ∧
    ∫ r, averagedRetrieval ρ c fT (F r) GA GB vabs T ∂P =
      ((2 / (ρ * c) : ℝ) : ℂ) * ∫ x', ∫ x'', stackKernel P F x' x'' *
        (windowKernel fT vabs T x' x'' : ℂ) * (starRingEnd ℂ (GA x') * GB x'') := by
  refine ⟨fun x' x'' => ?_, fun x' x'' hx => ?_, ?_⟩
  · unfold windowKernel windowAvg; congr 1; funext τ; ring
  · unfold windowKernel windowAvg
    have : ∀ τ : ℝ, fT τ • ((if |x' - vabs * τ| ≤ T * vabs then (1:ℝ) else 0) *
        (if |x'' - vabs * τ| ≤ T * vabs then (1:ℝ) else 0)) = 0 := by
      intro τ
      split_ifs with h1 h2
      · exfalso
        have : |x' - x''| ≤ |x' - vabs * τ| + |x'' - vabs * τ| := by
          calc |x' - x''| = |(x' - vabs * τ) - (x'' - vabs * τ)| := by ring_nf
            _ ≤ _ := abs_sub _ _
        linarith
      all_goals simp
    simp only [this]; simp
  -- part 3
  set S : ℝ → Set ℝ := fun τ => {y : ℝ | |y - vabs * τ| ≤ T * vabs} with hS
  set K : ℝ → ℝ × ℝ → ℝ := fun τ p =>
    (S τ).indicator (fun _ => (1:ℝ)) p.1 * (S τ).indicator (fun _ => (1:ℝ)) p.2 with hK
  set Q : Ω → ℝ × ℝ → ℂ := fun r p => starRingEnd ℂ (F r p.1 * GA p.1) * (F r p.2 * GB p.2) with hQ
  set μ2 : Measure (ℝ × ℝ) := volume.prod volume
  have hKm : Measurable (fun z : ℝ × (ℝ × ℝ) => K z.1 z.2) := by
    simp only [K, S, Set.indicator, Set.mem_setOf_eq]
    apply Measurable.mul
    · exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) measurable_const measurable_const
    · exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) measurable_const measurable_const
  have hK01 : ∀ τ p, 0 ≤ K τ p ∧ K τ p ≤ 1 := by
    intro τ p
    simp only [K, Set.indicator]
    split_ifs <;> norm_num
  have hQm : Measurable (fun q : Ω × (ℝ × ℝ) => Q q.1 q.2) := by
    have h1 : Measurable (fun q : Ω × (ℝ × ℝ) => F q.1 q.2.1) :=
      hF.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have h2 : Measurable (fun q : Ω × (ℝ × ℝ) => F q.1 q.2.2) :=
      hF.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    exact (Complex.continuous_conj.measurable.comp (h1.mul (hGA.comp
      (measurable_fst.comp measurable_snd)))).mul (h2.mul (hGB.comp (measurable_snd.comp measurable_snd)))
  have hfTi : Integrable fT := by
    by_contra h
    have := integral_undef h
    rw [hf.2.2.1] at this; norm_num at this
  -- Step A
  have hA : ∀ r, averagedRetrieval ρ c fT (F r) GA GB vabs T = ((2 / (ρ * c) : ℝ) : ℂ) *
      ∫ τ, ∫ p, ((fT τ * K τ p : ℝ) : ℂ) * Q r p ∂μ2 := by
    intro r
    unfold averagedRetrieval windowAvg windowedRetrieval ambientRetrieval windowedRecording
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun τ => ?_))
    simp only
    rw [recprod]
    rw [Complex.real_smul, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    simp only [K, Q, S]; push_cast; ring
  set H : Ω → ℝ → ℝ × ℝ → ℂ := fun r τ p => ((fT τ * K τ p : ℝ) : ℂ) * Q r p with hH
  rw [integral_congr_ae (Filter.Eventually.of_forall hA), integral_const_mul]
  congr 1
  have hR : ∀ x' x'' : ℝ, stackKernel P F x' x'' * (windowKernel fT vabs T x' x'' : ℂ) *
      (starRingEnd ℂ (GA x') * GB x'') = ∫ r, ∫ τ, H r τ (x', x'') ∂volume ∂P := by
    intro x' x''
    unfold stackKernel windowKernel windowAvg
    rw [← integral_complex_ofReal, ← integral_mul_const, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
    simp only
    rw [← integral_const_mul, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun τ => ?_))
    simp only [H, K, Q, S, Set.indicator, Set.mem_setOf_eq, smul_eq_mul, map_mul]
    split_ifs <;> push_cast <;> ring
  simp_rw [hR]
  have hfm := hf.1
  have I1 : ∀ᵐ r ∂P, Integrable (fun z : ℝ × (ℝ × ℝ) => H r z.1 z.2) (volume.prod μ2) := by
    filter_upwards [hfub.prod_right_ae] with r hr
    refine Integrable.mono' (hfTi.mul_prod hr.norm) ?_ (Filter.Eventually.of_forall (fun z => ?_))
    · exact ((Complex.measurable_ofReal.comp ((hfm.comp measurable_fst).mul hKm)).mul
        (hQm.comp (measurable_const.prodMk measurable_snd))).aestronglyMeasurable
    · have e : ‖H r z.1 z.2‖ = fT z.1 * K z.1 z.2 * ‖Q r z.2‖ := by
        simp only [H]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (hf.2.1 _) (hK01 _ _).1)]
      rw [e]
      have : fT z.1 * K z.1 z.2 ≤ fT z.1 := by nlinarith [(hK01 z.1 z.2).1, (hK01 z.1 z.2).2, hf.2.1 z.1]
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  rw [integral_congr_ae (by filter_upwards [I1] with r hr; exact integral_integral_swap hr)]
  set cK : ℝ × ℝ → ℝ := fun p => ∫ τ, fT τ * K τ p with hcK
  have hcm : StronglyMeasurable cK := by
    refine StronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
      (f := fun z : (ℝ × ℝ) × ℝ => fT z.2 * K z.2 z.1) ?_
    exact ((hfm.comp measurable_snd).mul (hKm.comp (measurable_snd.prodMk measurable_fst))).stronglyMeasurable
  have hcb : ∀ p, ‖cK p‖ ≤ 1 := by
    intro p
    have hi : Integrable (fun τ => fT τ * K τ p) := by
      refine Integrable.mono' hfTi ?_ (Filter.Eventually.of_forall (fun τ => ?_))
      · exact (hfm.mul (hKm.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf.2.1 _), abs_of_nonneg (hK01 _ _).1]
        nlinarith [hK01 τ p, hf.2.1 τ]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun τ => mul_nonneg (hf.2.1 τ) (hK01 τ p).1))]
    calc cK p ≤ ∫ τ, fT τ := integral_mono hi hfTi (fun τ => by nlinarith [hK01 τ p, hf.2.1 τ])
      _ = 1 := hf.2.2.1
  have hG : ∀ r p, ∫ τ, ((fT τ * K τ p : ℝ) : ℂ) * Q r p = (cK p : ℂ) * Q r p := by
    intro r p
    simp only [cK]
    rw [integral_mul_const, integral_complex_ofReal]
  simp_rw [hG]
  have I2 : Integrable (Function.uncurry fun r p => (cK p : ℂ) * Q r p) (P.prod μ2) := by
    refine hfub.bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall (fun q => ?_))
    · exact (Complex.measurable_ofReal.comp (hcm.measurable.comp measurable_snd)).aestronglyMeasurable
    · simpa [Complex.norm_real] using hcb q.2
  rw [integral_integral_swap I2]
  have I3 : Integrable (fun p => ∫ r, (cK p : ℂ) * Q r p ∂P) μ2 := by
    simp_rw [integral_const_mul]
    refine (hfub.integral_prod_right).bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall (fun p => ?_))
    · exact (Complex.measurable_ofReal.comp hcm.measurable).aestronglyMeasurable
    · simpa [Complex.norm_real] using hcb p
  simp only [hH]
  simp_rw [hG]
  exact integral_prod _ I3
