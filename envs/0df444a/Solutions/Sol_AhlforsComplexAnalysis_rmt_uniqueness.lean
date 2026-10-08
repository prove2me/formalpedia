-- Prove2me | solution 1 for AhlforsComplexAnalysis.rmt_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T12:35:32.310985+00:00
-- url     : https://prove2.me/submissions/705754d8-660d-4dd6-9db2-f6f2f542a094

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Defs
import Theorems.Thm_AhlforsComplexAnalysis_schwarz_lemma
import Theorems.Thm_AhlforsComplexAnalysis_deriv_ne_zero_of_injOn

set_option autoImplicit false

open Set Filter Topology

namespace AhlforsUniq

/-- If `f` is analytic and injective on the region `Ω` with image the unit disk, then every analytic
function on `Ω` factors through `f` via an analytic function on the disk. -/
theorem rmtU_exists_comp_inv {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω) (hinj : InjOn f Ω) (himg : f '' Ω = Metric.ball 0 1)
    (hg : AnalyticOnNhd ℂ g Ω) :
    ∃ φ : ℂ → ℂ, AnalyticOnNhd ℂ φ (Metric.ball 0 1) ∧ ∀ z ∈ Ω, φ (f z) = g z := by
  classical
  set finv : ℂ → ℂ := Function.invFunOn f Ω with hfinv
  have hfinv_f : ∀ c ∈ Ω, finv (f c) = c := fun c hc => hinj.leftInvOn_invFunOn hc
  have hfinv_mem : ∀ w ∈ Metric.ball (0 : ℂ) 1, finv w ∈ Ω ∧ f (finv w) = w := by
    intro w hw
    rw [← himg] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    exact Function.invFunOn_pos ⟨a, ha, rfl⟩
  have hopen : ∀ s ⊆ Ω, IsOpen s → IsOpen (f '' s) := by
    rcases hf.is_constant_or_isOpen hΩc with ⟨w, hw⟩ | h
    · exfalso
      have h0 : (0 : ℂ) ∈ f '' Ω := by rw [himg]; simp
      have h1 : (1 / 2 : ℂ) ∈ f '' Ω := by
        rw [himg, mem_ball_zero_iff]
        norm_num
      obtain ⟨a, ha, ha0⟩ := h0
      obtain ⟨b, hb, hb0⟩ := h1
      rw [hw a ha] at ha0
      rw [hw b hb] at hb0
      rw [ha0] at hb0
      norm_num at hb0
    · exact h
  have hcont : ∀ w ∈ Metric.ball (0 : ℂ) 1, ContinuousAt finv w := by
    intro w hw
    obtain ⟨c, hcΩ, rfl⟩ : ∃ c ∈ Ω, f c = w := by
      rw [← himg] at hw
      exact hw
    rw [ContinuousAt, hfinv_f c hcΩ]
    rw [tendsto_nhds]
    intro s hs hcs
    have hopen' : IsOpen (f '' (s ∩ Ω)) := hopen _ inter_subset_right (hs.inter hΩo)
    refine Filter.mem_of_superset (hopen'.mem_nhds ⟨c, ⟨hcs, hcΩ⟩, rfl⟩) ?_
    rintro _ ⟨z, ⟨hzs, hzΩ⟩, rfl⟩
    simp only [mem_preimage]
    rw [hfinv_f z hzΩ]
    exact hzs
  have hdiff : ∀ w ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℂ finv w := by
    intro w hw
    obtain ⟨hwΩ, hfw⟩ := hfinv_mem w hw
    have hd0 : deriv f (finv w) ≠ 0 :=
      AhlforsComplexAnalysis.deriv_ne_zero_of_injOn (hΩo.mem_nhds hwΩ) (hf _ hwΩ) hinj
    have hfd : HasDerivAt f (deriv f (finv w)) (finv w) := (hf _ hwΩ).differentiableAt.hasDerivAt
    have hev : ∀ᶠ y in 𝓝 w, f (finv y) = y := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw] with y hy
      exact (hfinv_mem y hy).2
    exact (HasDerivAt.of_local_left_inverse (hcont w hw) hfd hd0 hev).differentiableAt
  refine ⟨fun w => g (finv w), ?_, fun z hz => by simp [hfinv_f z hz]⟩
  refine DifferentiableOn.analyticOnNhd ?_ Metric.isOpen_ball
  intro w hw
  exact ((hg _ (hfinv_mem w hw).1).differentiableAt.comp w (hdiff w hw)).differentiableWithinAt

/-- Data extracted from Schwarz's lemma for `φ = g ∘ f⁻¹`. -/
theorem rmtU_schwarz_data {Ω : Set ℂ} (hΩ : AhlforsComplexAnalysis.IsRegion Ω) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) (hf0 : f z₀ = 0)
    (hinj : InjOn f Ω) (himg : f '' Ω = Metric.ball 0 1) (hg : AnalyticOnNhd ℂ g Ω)
    (hg0 : g z₀ = 0) (hgD : ∀ z ∈ Ω, g z ∈ Metric.ball (0 : ℂ) 1) :
    ∃ φ : ℂ → ℂ, AnalyticOnNhd ℂ φ (Metric.ball 0 1) ∧ (∀ z ∈ Ω, φ (f z) = g z) ∧
      deriv g z₀ = deriv φ 0 * deriv f z₀ ∧ ‖deriv φ 0‖ ≤ 1 ∧
      (‖deriv φ 0‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ w ∈ Metric.ball (0 : ℂ) 1, φ w = c * w) := by
  obtain ⟨φ, hφ, hφf⟩ := rmtU_exists_comp_inv hΩ.1 hΩ.2.isPreconnected hf hinj himg hg
  have hbound : ∀ w ∈ Metric.ball (0 : ℂ) 1, ‖φ w‖ ≤ 1 := by
    intro w hw
    rw [← himg] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    rw [hφf a ha]
    exact (mem_ball_zero_iff.mp (hgD a ha)).le
  have hφ0 : φ 0 = 0 := by
    have := hφf z₀ hz₀
    rwa [hf0, hg0] at this
  obtain ⟨-, hle, heq⟩ := AhlforsComplexAnalysis.schwarz_lemma hφ hbound hφ0
  refine ⟨φ, hφ, hφf, ?_, hle, fun h1 => heq (Or.inr h1)⟩
  have hΩn : Ω ∈ 𝓝 z₀ := hΩ.1.mem_nhds hz₀
  have hφd : DifferentiableAt ℂ φ (f z₀) := by
    rw [hf0]
    exact (hφ 0 (by simp)).differentiableAt
  have hfd : DifferentiableAt ℂ f z₀ := (hf z₀ hz₀).differentiableAt
  have hev : g =ᶠ[𝓝 z₀] φ ∘ f := by
    filter_upwards [hΩn] with z hz
    exact (hφf z hz).symm
  rw [hev.deriv_eq, deriv_comp z₀ hφd hfd, hf0]

/-- The norm of a complex number with zero imaginary part and positive real part is its real part. -/
theorem rmtU_norm_eq_re {z : ℂ} (him : z.im = 0) (hre : 0 < z.re) : ‖z‖ = z.re := by
  rw [← Complex.abs_re_eq_norm.mpr him, abs_of_pos hre]

theorem rmt_uniqueness {Ω : Set ℂ} (hΩ : AhlforsComplexAnalysis.IsRegion Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω ∧ f z₀ = 0 ∧ 0 < (deriv f z₀).re ∧ (deriv f z₀).im = 0 ∧
      Set.InjOn f Ω ∧ f '' Ω = Metric.ball 0 1)
    (hg : AnalyticOnNhd ℂ g Ω ∧ g z₀ = 0 ∧ 0 < (deriv g z₀).re ∧ (deriv g z₀).im = 0 ∧
      Set.InjOn g Ω ∧ g '' Ω = Metric.ball 0 1) :
    Set.EqOn f g Ω := by
  obtain ⟨hfa, hf0, hfre, hfim, hfinj, hfimg⟩ := hf
  obtain ⟨hga, hg0, hgre, hgim, hginj, hgimg⟩ := hg
  have hfD : ∀ z ∈ Ω, f z ∈ Metric.ball (0 : ℂ) 1 := fun z hz => hfimg ▸ mem_image_of_mem f hz
  have hgD : ∀ z ∈ Ω, g z ∈ Metric.ball (0 : ℂ) 1 := fun z hz => hgimg ▸ mem_image_of_mem g hz
  obtain ⟨φ, hφ, hφf, hchain, hle, heq⟩ :=
    rmtU_schwarz_data hΩ hz₀ hfa hf0 hfinj hfimg hga hg0 hgD
  obtain ⟨ψ, hψ, hψg, hchain', hle', -⟩ :=
    rmtU_schwarz_data hΩ hz₀ hga hg0 hginj hgimg hfa hf0 hfD
  have h1 : ‖deriv g z₀‖ ≤ ‖deriv f z₀‖ := by
    rw [hchain, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hle
  have h2 : ‖deriv f z₀‖ ≤ ‖deriv g z₀‖ := by
    rw [hchain', norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hle'
  have hderiv : deriv g z₀ = deriv f z₀ := by
    have hn : ‖deriv g z₀‖ = ‖deriv f z₀‖ := le_antisymm h1 h2
    rw [rmtU_norm_eq_re hgim hgre, rmtU_norm_eq_re hfim hfre] at hn
    exact Complex.ext hn (by rw [hgim, hfim])
  have hd0 : deriv f z₀ ≠ 0 := by
    intro h0
    rw [h0] at hfre
    simp at hfre
  have hφ1 : deriv φ 0 = 1 := by
    have : deriv φ 0 * deriv f z₀ = 1 * deriv f z₀ := by rw [one_mul, ← hchain, hderiv]
    exact mul_right_cancel₀ hd0 this
  obtain ⟨c, hc, hφc⟩ := heq (by rw [hφ1, norm_one])
  have hc1 : c = 1 := by
    have hev : φ =ᶠ[𝓝 0] fun w => c * w := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)] with w hw
      exact hφc w hw
    have : deriv φ 0 = c := by
      rw [hev.deriv_eq]
      simp
    rw [← this, hφ1]
  intro z hz
  have := hφf z hz
  rw [hφc _ (hfD z hz), hc1, one_mul] at this
  exact this

end AhlforsUniq

theorem solution {Ω : Set ℂ} (hΩ : AhlforsComplexAnalysis.IsRegion Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω ∧ f z₀ = 0 ∧ 0 < (deriv f z₀).re ∧ (deriv f z₀).im = 0 ∧
      Set.InjOn f Ω ∧ f '' Ω = Metric.ball 0 1)
    (hg : AnalyticOnNhd ℂ g Ω ∧ g z₀ = 0 ∧ 0 < (deriv g z₀).re ∧ (deriv g z₀).im = 0 ∧
      Set.InjOn g Ω ∧ g '' Ω = Metric.ball 0 1) :
    Set.EqOn f g Ω :=
  AhlforsUniq.rmt_uniqueness hΩ hz₀ hf hg

#print axioms solution
