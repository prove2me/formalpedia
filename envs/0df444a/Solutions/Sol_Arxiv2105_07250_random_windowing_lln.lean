-- Prove2me | solution 1 for Arxiv2105_07250.random_windowing_lln
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T08:42:39.131265+00:00
-- url     : https://prove2.me/submissions/5b24d05b-2a41-4d98-8cc0-18c17343a783

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section
namespace RW
open Arxiv2105_07250

lemma rec_meas (F G : ℝ → ℂ) (hFG : Integrable (fun x' : ℝ => F x' * G x')) (vabs T : ℝ) :
    StronglyMeasurable (fun τ => windowedRecording F G vabs T τ) := by
  set q := hFG.aestronglyMeasurable.mk _
  have hq : (fun x' : ℝ => F x' * G x') =ᵐ[volume] q := hFG.aestronglyMeasurable.ae_eq_mk
  have hqm : StronglyMeasurable q := hFG.aestronglyMeasurable.stronglyMeasurable_mk
  have e : (fun τ => windowedRecording F G vabs T τ) =
      fun τ => ∫ y, (fun p : ℝ × ℝ => if |p.2 - vabs * p.1| ≤ T * vabs then q p.2 else 0) (τ, y) := by
    funext τ
    unfold windowedRecording
    apply integral_congr_ae
    filter_upwards [hq] with y hy
    simp only [Set.indicator, Set.mem_setOf_eq]
    split_ifs <;> simp [hy]
  rw [e]
  refine StronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
    (f := fun p : ℝ × ℝ => if |p.2 - vabs * p.1| ≤ T * vabs then q p.2 else 0) ?_
  apply StronglyMeasurable.ite
  · apply measurableSet_le
    · fun_prop
    · fun_prop
  · exact hqm.comp_measurable measurable_snd
  · exact stronglyMeasurable_const

lemma rec_bd (F G : ℝ → ℂ) (hFG : Integrable (fun x' : ℝ => F x' * G x')) (vabs T τ : ℝ) :
    ‖windowedRecording F G vabs T τ‖ ≤ ∫ y, ‖F y * G y‖ := by
  unfold windowedRecording
  apply norm_integral_le_of_norm_le hFG.norm
  exact Filter.Eventually.of_forall (fun y => norm_indicator_le_norm_self _ _)

end RW

open Arxiv2105_07250 RW in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c) (F GA GB : ℝ → ℂ)
    (hFA : Integrable (fun x' : ℝ => F x' * GA x')) (hFB : Integrable (fun x' : ℝ => F x' * GB x'))
    (vabs T t0 : ℝ) (hv : 0 < vabs) (hT : 0 < T) (fT : ℝ → ℝ) (hf : IsWindowDensity fT)
    (hmean : ∫ τ, τ * fT τ = t0) (hvar : Integrable (fun τ : ℝ => τ ^ 2 * fT τ))
    (t : ℕ → Ω → ℝ) (ht : ∀ n, Measurable (t n))
    (hlaw : ∀ n, P.map (t n) = volume.withDensity (fun τ => ENNReal.ofReal (fT τ)))
    (hind : iIndepFun t P) :
    ∀ᵐ r ∂P, Tendsto (fun N : ℕ => (1 / (N : ℂ)) *
        ∑ n ∈ Finset.range N, windowedRetrieval ρ c F GA GB vabs T (t n r)) atTop
      (𝓝 (averagedRetrieval ρ c fT F GA GB vabs T)) := by
  set φ : ℝ → ℂ := fun τ => windowedRetrieval ρ c F GA GB vabs T τ with hφ
  have hφm : Measurable φ := by
    have a := (rec_meas F GA hFA vabs T).measurable
    have b := (rec_meas F GB hFB vabs T).measurable
    have : φ = fun τ => ((2 / (ρ * c) : ℝ) : ℂ) *
        (starRingEnd ℂ (windowedRecording F GA vabs T τ) * windowedRecording F GB vabs T τ) := rfl
    rw [this]
    exact measurable_const.mul ((Complex.continuous_conj.measurable.comp a).mul b)
  set B : ℝ := |2 / (ρ * c)| * ((∫ y, ‖F y * GA y‖) * (∫ y, ‖F y * GB y‖))
  have hφb : ∀ τ, ‖φ τ‖ ≤ B := by
    intro τ
    show ‖((2 / (ρ * c) : ℝ) : ℂ) * (starRingEnd ℂ (windowedRecording F GA vabs T τ) *
      windowedRecording F GB vabs T τ)‖ ≤ B
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact mul_le_mul (rec_bd F GA hFA vabs T τ) (rec_bd F GB hFB vabs T τ) (norm_nonneg _)
      (integral_nonneg (fun _ => norm_nonneg _))
  let X : ℕ → Ω → ℂ := fun n r => φ (t n r)
  have hint : Integrable (X 0) P :=
    Integrable.of_bound ((hφm.comp (ht 0)).aestronglyMeasurable) B
      (Filter.Eventually.of_forall (fun r => hφb _))
  have hindep : Pairwise (Function.onFun (fun f g => IndepFun f g P) X) := by
    intro i j hij
    exact (hind.indepFun hij).comp hφm hφm
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := by
    intro i
    have : IdentDistrib (t i) (t 0) P P :=
      ⟨(ht i).aemeasurable, (ht 0).aemeasurable, by rw [hlaw, hlaw]⟩
    exact this.comp hφm
  have hsl := strong_law_ae X hint hindep hident
  have hE : P[X 0] = averagedRetrieval ρ c fT F GA GB vabs T := by
    show ∫ r, φ (t 0 r) ∂P = _
    rw [← integral_map (ht 0).aemeasurable hφm.aestronglyMeasurable, hlaw 0]
    have e : (fun τ => ENNReal.ofReal (fT τ)) = fun τ => ((Real.toNNReal (fT τ) : NNReal) : ENNReal) := rfl
    rw [e, integral_withDensity_eq_integral_smul (hf.1.real_toNNReal)]
    unfold averagedRetrieval windowAvg
    refine integral_congr_ae (Filter.Eventually.of_forall (fun τ => ?_))
    simp only
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hf.2.1 τ)]
  rw [hE] at hsl
  filter_upwards [hsl] with r hr
  refine hr.congr (fun N => ?_)
  simp only [X, φ]
  rw [Complex.real_smul]; push_cast; rw [one_div]
