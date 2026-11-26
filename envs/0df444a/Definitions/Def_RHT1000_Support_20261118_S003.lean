-- Prove2me | Definitions.Def_RHT1000_Support_20261118_S003
-- name    : RHT1000_Support_20261118_S003
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-18T17:56:09.497629+00:00
-- url     : https://prove2.me/theorems/2df1fce8-f28a-454c-b370-061afd232789
-- title:
--   Suporte completo para T1000 — bloco 8 de 10
-- statement:
--   Definições e lemas auxiliares completos para a prova finita T1000. Este bloco não afirma sozinho a conclusão T1000 nem RH. A divisão reduz o tempo de compilação sem substituir demonstrações por hipóteses.
-- source:
--   Código adaptado de Salvatore Mercuri e Bhavik Mehta, smmercuri/zeta, tag v1-1e8 (3dab648), com dependências e avisos de autoria preservados. Fonte histórica integral T1000: https://axle.axiommath.ai/check#r=d2dcb520-c50a-44dc-a527-de0f7a51b892 . Reorganização em módulos ordinários para compatibilidade com Prove2Me; atribuição da adaptação: projeto Desenvolvimento RH, Ricardo Marangoni Brandão Bueno.

import Definitions.Def_RHT1000_Support_20261118_S002
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
section CertificatePort121
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
theorem hasDerivAt_contourIntegrand {a : ℝ} (ha0 : 0 < a) (s : ℂ) (w : ℝ) :
    HasDerivAt (fun u ↦ contourIntegrand u a w)
      (-slantLog (line a w) * contourIntegrand s a w) s := by
  have hexp : ∀ u : ℂ, contourIntegrand u a w
      = exp (-u * slantLog (line a w)) * kernel (line a w) := fun u ↦ by
    rw [contourIntegrand, integrand, slantCpow_eq_exp_mul_slantLog (line_ne_zero ha0.ne' w)]
  simp only [hexp]
  exact (((hasDerivAt_neg' (𝕜 := ℂ) s).mul_const (slantLog (line a w))).cexp.mul_const
    (kernel (line a w))).congr_deriv (by ring)
theorem differentiable_contourIntegral {a c : ℝ} (ha0 : 0 < a) (hc : 0 < c)
    (hsin : ∀ w : ℝ, c ≤ ‖sin (π * line a w)‖) :
    Differentiable ℂ fun s ↦ contourIntegral s a := by
  have hsin0 : ∀ w : ℝ, sin (π * line a w) ≠ 0 := fun w ↦
    norm_pos_iff.1 (lt_of_lt_of_le hc (hsin w))
  intro s₀
  simp only [contourIntegral]
  obtain ⟨M, hMle⟩ : ∃ M : ℝ, ∀ s : ℂ, |s.re| ≤ |s₀.re| + 1 → |s.im| ≤ |s₀.im| + 1 →
      ∀ w : ℝ, ‖contourIntegrand s a w‖ ≤ M * Real.exp (-(π / 2) * w ^ 2) :=
    ⟨_, fun _ ↦ norm_contourIntegrand_le_exp ha0 hc hsin⟩
  obtain ⟨N, hN0, hNle⟩ : ∃ N : ℝ, 0 < N ∧ ∀ w : ℝ, ‖slantLog (line a w)‖ ≤ N + 2 * |w| :=
    ⟨_, by positivity, norm_slantLog_line_le ha0⟩
  have hint : Integrable fun w : ℝ ↦ Real.exp (-(π / 2) * w ^ 2) * (M * N + 2 * M * |w|) := by
    simpa using integrable_exp_neg_mul_sq_mul_poly (by positivity) (M * N) (2 * M) 0 0
  have hbound : ∀ w : ℝ, ∀ s ∈ Metric.ball s₀ 1,
      ‖-slantLog (line a w) * contourIntegrand s a w‖
        ≤ Real.exp (-(π / 2) * w ^ 2) * (M * N + 2 * M * |w|) := by
    intro w s hs
    have hd : ‖s - s₀‖ ≤ 1 := by rw [Metric.mem_ball, Complex.dist_eq] at hs; exact hs.le
    have hre : |s.re| ≤ |s₀.re| + 1 := sub_le_iff_le_add'.1 <|
      ((abs_sub_abs_le_abs_sub s.re s₀.re).trans
        (by simpa using Complex.abs_re_le_norm (s - s₀))).trans hd
    have him : |s.im| ≤ |s₀.im| + 1 := sub_le_iff_le_add'.1 <|
      ((abs_sub_abs_le_abs_sub s.im s₀.im).trans
        (by simpa using Complex.abs_im_le_norm (s - s₀))).trans hd
    rw [norm_mul, norm_neg]
    calc ‖slantLog (line a w)‖ * ‖contourIntegrand s a w‖
        ≤ (N + 2 * |w|) * (M * Real.exp (-(π / 2) * w ^ 2)) :=
          mul_le_mul (hNle w) (hMle s hre him w) (norm_nonneg _) (by linarith [abs_nonneg w])
      _ = _ := by ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := s₀)
    (F := fun (s : ℂ) (w : ℝ) ↦ contourIntegrand s a w)
    (F' := fun (s : ℂ) (w : ℝ) ↦ -slantLog (line a w) * contourIntegrand s a w)
    (bound := fun w ↦ Real.exp (-(π / 2) * w ^ 2) * (M * N + 2 * M * |w|))
    (s := Metric.ball s₀ 1) (Metric.ball_mem_nhds s₀ one_pos)
    (Filter.Eventually.of_forall fun s ↦
      (continuous_contourIntegrand s ha0 hsin0).aestronglyMeasurable)
    (integrable_contourIntegrand s₀ ha0 hc hsin)
    (((continuous_slantLog_line ha0).neg.mul
      (continuous_contourIntegrand s₀ ha0 hsin0)).aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound)
    hint
    (Filter.Eventually.of_forall fun w s _ ↦
      hasDerivAt_contourIntegrand ha0 s w)).2.differentiableAt.const_mul (1 + I)
theorem differentiable_contourIntegral_of_le_half {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    Differentiable ℂ fun s ↦ contourIntegral s a :=
  differentiable_contourIntegral ha0 (c := min (1 / 2) (a / Real.sqrt 2))
    (lt_min (by norm_num) (by positivity))
    fun w ↦ (min_le_min le_rfl (norm_line_ge a w)).trans
      (norm_sin_pi_mul_line_ge_min ha0.le ha w)
end Zeta.RiemannSiegel
end
end CertificatePort121


section CertificatePort122
section
open Filter MeasureTheory Set Topology
open scoped Real
namespace Real
theorem integrableOn_rpow_mul_exp_neg_mul_Ioi {c δ : ℝ} (hc : -1 < c) (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ ↦ t ^ c * exp (-δ * t)) (Ioi 0) := by
  simpa using integrableOn_rpow_mul_exp_neg_mul_rpow hc one_pos hδ
end Real
namespace Complex
theorem integrableOn_cpow_mul_exp_neg_mul_Ioi {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (a - 1) * exp (-(b * t))) (Ioi 0) := by
  refine (Real.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith : (-1 : ℝ) < a.re - 1) hb).mono'
    (ContinuousOn.aestronglyMeasurable (ContinuousOn.mul (fun t ht ↦ ?_) (by fun_prop))
      measurableSet_Ioi) ?_
  · exact (continuousAt_ofReal_cpow_const t (a - 1) (Or.inr (mem_Ioi.1 ht).ne')).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (mem_Ioi.1 ht), norm_exp]
    simp [mul_re, neg_mul]
theorem integral_cpow_mul_exp_neg_mul_Ioi' {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (a - 1) * exp (-(b * t)) = (1 / b) ^ a * Gamma a := by
  set F : ℂ → ℂ := fun z ↦ ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (a - 1) * exp (-(z * t)) with hF
  set G : ℂ → ℂ := fun z ↦ (1 / z) ^ a * Gamma a with hG
  have hUopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hFdiff : ∀ z ∈ {z : ℂ | 0 < z.re}, DifferentiableAt ℂ F z := by
    intro b₀ hb₀
    have hb₀' : 0 < b₀.re := hb₀
    have hδ : 0 < b₀.re / 2 := by positivity
    have hball : ∀ z ∈ Metric.ball b₀ (b₀.re / 2), b₀.re / 2 ≤ z.re := by
      intro z hz
      have h1 : |(z - b₀).re| ≤ ‖z - b₀‖ := abs_re_le_norm _
      have h2 : ‖z - b₀‖ < b₀.re / 2 := by simpa [dist_eq] using hz
      have h3 : |z.re - b₀.re| < b₀.re / 2 := by simpa [sub_re] using h1.trans_lt h2
      linarith [(abs_lt.1 h3).1]
    have hbound := Real.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith : (-1 : ℝ) < a.re) hδ
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (volume : Measure ℝ).restrict (Ioi 0))
      (F := fun (z : ℂ) (t : ℝ) ↦ (t : ℂ) ^ (a - 1) * exp (-(z * t)))
      (F' := fun (z : ℂ) (t : ℝ) ↦ -(t : ℂ) * ((t : ℂ) ^ (a - 1) * exp (-(z * t))))
      (x₀ := b₀) (bound := fun t : ℝ ↦ t ^ a.re * Real.exp (-(b₀.re / 2) * t))
      (Metric.ball_mem_nhds b₀ hδ)
      (eventually_of_mem (Metric.ball_mem_nhds b₀ hδ) fun z hz ↦
        MeasureTheory.Integrable.aestronglyMeasurable
          (integrableOn_cpow_mul_exp_neg_mul_Ioi ha (lt_of_lt_of_le hδ (hball z hz))))
      (integrableOn_cpow_mul_exp_neg_mul_Ioi ha hb₀')
      (continuous_ofReal.neg.aestronglyMeasurable.mul
        (integrableOn_cpow_mul_exp_neg_mul_Ioi ha hb₀').aestronglyMeasurable)
      ?_ hbound ?_
    · exact key.2.differentiableAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
      have ht0 : (0 : ℝ) < t := mem_Ioi.1 ht
      have h1 : t * t ^ (a.re - 1) = t ^ a.re := by
        rw [mul_comm, ← Real.rpow_add_one ht0.ne']
        congr 1
        ring
      have h2 : (-(z * (t : ℂ))).re = -(z.re * t) := by simp [mul_re]
      rw [norm_mul, norm_mul, norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos ht0,
        norm_cpow_eq_rpow_re_of_pos ht0, norm_exp, h2, sub_re, one_re, ← mul_assoc, h1]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg ht0.le _)
      rw [neg_mul]
      exact neg_le_neg (mul_le_mul_of_nonneg_right (hball z hz) ht0.le)
    · filter_upwards with t z _
      have h0 : HasDerivAt (fun z : ℂ ↦ z * (t : ℂ)) ((t : ℂ)) z := by
        simpa using (hasDerivAt_id z).mul_const ((t : ℂ))
      exact ((h0.neg.cexp).const_mul ((t : ℂ) ^ (a - 1))).congr_deriv
        (by simp only [Pi.neg_apply]; ring)
  have hGdiff : ∀ z ∈ {z : ℂ | 0 < z.re}, DifferentiableAt ℂ G z := by
    intro b₀ hb₀
    have hb₀' : 0 < b₀.re := hb₀
    have hne : b₀ ≠ 0 := fun h ↦ by simp [h] at hb₀'
    have hslit : (1 / b₀) ∈ slitPlane := by
      refine mem_slitPlane_iff.2 (Or.inl ?_)
      rw [one_div, inv_re]
      exact div_pos hb₀' (normSq_pos.2 hne)
    exact ((differentiableAt_const 1 |>.div differentiableAt_id hne).cpow_const hslit).mul_const _
  have hFan : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.re} :=
    DifferentiableOn.analyticOnNhd (fun z hz ↦ (hFdiff z hz).differentiableWithinAt) hUopen
  have hGan : AnalyticOnNhd ℂ G {z : ℂ | 0 < z.re} :=
    DifferentiableOn.analyticOnNhd (fun z hz ↦ (hGdiff z hz).differentiableWithinAt) hUopen
  have hone : (1 : ℂ) = ((1 : ℝ) : ℂ) := by norm_num
  have hagree : ∃ᶠ z in 𝓝[≠] (1 : ℂ), F z = G z := by
    rw [Filter.frequently_iff]
    intro s hs
    rw [mem_nhdsWithin] at hs
    obtain ⟨u, huopen, h1u, hus⟩ := hs
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 huopen 1 h1u
    have hr : (0 : ℝ) < 1 + ε / 2 := by linarith
    refine ⟨((1 + ε / 2 : ℝ) : ℂ), hus ⟨hball ?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, hone, dist_eq, ← ofReal_sub, norm_real, Real.norm_eq_abs,
        show (1 + ε / 2 - 1 : ℝ) = ε / 2 by ring, abs_of_pos (by linarith)]
      linarith
    · simp only [mem_compl_iff, mem_singleton_iff, hone, ofReal_inj]
      intro hcon
      linarith
    · simp only [hF, hG]
      exact integral_cpow_mul_exp_neg_mul_Ioi ha hr
  exact hFan.eqOn_of_preconnected_of_frequently_eq hGan
    (convex_halfSpace_re_gt 0).isPreconnected (by simp) hagree hb
theorem integral_cpow_neg_mul_exp_neg_mul_Ioi {s b : ℂ} (hs : s.re < 1) (hb : 0 < b.re) :
    ∫ ρ : ℝ in Ioi 0, (ρ : ℂ) ^ (-s) * exp (-(b * ρ)) = Gamma (1 - s) * b ^ (s - 1) := by
  have ha : 0 < (1 - s).re := by simpa using hs
  have harg : b.arg ≠ π := fun h ↦ absurd (arg_eq_pi_iff.1 h).1 (not_lt.2 hb.le)
  have hpow : (1 / b) ^ (1 - s) = b ^ (s - 1) := by
    rw [one_div, inv_cpow _ _ harg, ← cpow_neg, neg_sub]
  calc ∫ ρ : ℝ in Ioi 0, (ρ : ℂ) ^ (-s) * exp (-(b * ρ))
      = (1 / b) ^ (1 - s) * Gamma (1 - s) := by
        simpa only [show (1 - s) - 1 = -s by ring] using integral_cpow_mul_exp_neg_mul_Ioi' ha hb
    _ = Gamma (1 - s) * b ^ (s - 1) := by rw [hpow]; ring
end Complex
namespace Real
theorem integral_rpow_neg_mul_exp_neg_mul_Ioi {c r : ℝ} (hc : c < 1) (hr : 0 < r) :
    ∫ ρ in Ioi (0 : ℝ), ρ ^ (-c) * exp (-(r * ρ)) = Gamma (1 - c) * r ^ (c - 1) := by
  have hint : ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (-(c : ℂ)) * Complex.exp (-((r : ℂ) * ρ))
      = ((∫ ρ in Ioi (0 : ℝ), ρ ^ (-c) * exp (-(r * ρ)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ ↦ ?_
    have hρ0 : (0 : ℝ) < ρ := hρ
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hρ0.le, Complex.ofReal_exp]
    push_cast
    ring
  have h := Complex.integral_cpow_neg_mul_exp_neg_mul_Ioi (s := (c : ℂ)) (b := (r : ℂ))
    (by simpa using hc) (by simpa using hr)
  rw [hint, show (1 : ℂ) - (c : ℂ) = ((1 - c : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
    show (c : ℂ) - 1 = ((c - 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hr.le,
    ← Complex.ofReal_mul] at h
  exact_mod_cast h
end Real
end
end CertificatePort122


section CertificatePort123
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def hankelIntegrand (s : ℂ) (ρ : ℝ) : ℂ :=
  (ρ : ℂ) ^ (-s) * exp (-(π * (ρ : ℂ) ^ 2)) / sin (π * ρ * exp ((π / 4 : ℝ) * I))
noncomputable def hankelIntegral (s : ℂ) : ℂ :=
  ∫ ρ in Set.Ioi (0 : ℝ), hankelIntegrand s ρ
theorem norm_sin_pi_mul_ray_ge' {ρ : ℝ} (hρ : 0 ≤ ρ) :
    π * ρ / Real.sqrt 2 ≤ ‖sin ((π : ℂ) * ρ * exp ((π / 4 : ℝ) * I))‖ := by
  have h := sinh_le_norm_sin_pi_mul_line 0 (ρ / Real.sqrt 2)
  rw [line_zero, show (Real.sqrt 2 * (ρ / Real.sqrt 2) : ℝ) = ρ by
      field_simp, ← mul_assoc, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ρ / Real.sqrt 2),
    ← mul_div_assoc] at h
  exact (Real.self_le_sinh_iff.2 (by positivity)).trans h
theorem continuousOn_hankelIntegrand (s : ℂ) :
    ContinuousOn (hankelIntegrand s) (Set.Ioi (0 : ℝ)) := by
  have hsin : ∀ ρ ∈ Set.Ioi (0 : ℝ), sin ((π : ℂ) * ρ * exp ((π / 4 : ℝ) * I)) ≠ 0 :=
    fun ρ (hρ : (0 : ℝ) < ρ) ↦
      norm_pos_iff.1 (lt_of_lt_of_le (by positivity) (norm_sin_pi_mul_ray_ge' hρ.le))
  refine ContinuousOn.div (ContinuousOn.mul ?_ (by fun_prop)) (by fun_prop) hsin
  exact ContinuousOn.cpow (by fun_prop) continuousOn_const fun ρ hρ ↦
    mem_slitPlane_iff.2 (Or.inl (by simpa using hρ))
theorem norm_hankelIntegrand_le (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ‖hankelIntegrand s ρ‖ ≤ Real.sqrt 2 / π * (ρ ^ (-s.re - 1) * Real.exp (-π * ρ ^ 2)) := by
  have hden := norm_sin_pi_mul_ray_ge' hρ.le
  rw [hankelIntegrand, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hρ,
    show (-((π : ℂ) * (ρ : ℂ) ^ 2)) = (((-π * ρ ^ 2 : ℝ)) : ℂ) by push_cast; ring,
    Complex.norm_exp, Complex.ofReal_re, Complex.neg_re]
  calc ρ ^ (-s.re) * Real.exp (-π * ρ ^ 2) / ‖sin ((π : ℂ) * ρ * exp ((π / 4 : ℝ) * I))‖
      ≤ ρ ^ (-s.re) * Real.exp (-π * ρ ^ 2) / (π * ρ / Real.sqrt 2) := by gcongr
    _ = Real.sqrt 2 / π * (ρ ^ (-s.re - 1) * Real.exp (-π * ρ ^ 2)) := by
        rw [Real.rpow_sub hρ, Real.rpow_one]
        field_simp
theorem integrableOn_hankelIntegrand {s : ℂ} (hs : s.re < 0) :
    IntegrableOn (hankelIntegrand s) (Set.Ioi (0 : ℝ)) := by
  refine Integrable.mono' ((integrableOn_rpow_mul_exp_neg_mul_sq Real.pi_pos
      (by linarith : (-1 : ℝ) < -s.re - 1)).const_mul (Real.sqrt 2 / π))
    ((continuousOn_hankelIntegrand s).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ using norm_hankelIntegrand_le s hρ
theorem exp_pi_mul_I_mul_ofReal_mul_exp_pi_div_four_mul_I_sq (ρ : ℝ) :
    exp ((π : ℂ) * I * ((ρ : ℂ) * exp ((π / 4 : ℝ) * I)) ^ 2) = exp (-(π * (ρ : ℂ) ^ 2)) := by
  congr 1
  linear_combination ((π : ℂ) * I * (ρ : ℂ) ^ 2) * Complex.exp_pi_div_four_mul_I_mul_self
    + ((π : ℂ) * (ρ : ℂ) ^ 2) * Complex.I_sq
theorem integrand_ofReal_mul_exp_pi_div_four_mul_I (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    integrand s ((ρ : ℂ) * exp ((π / 4 : ℝ) * I))
      = exp ((-(π / 4) : ℝ) * I * s) / (2 * I) * hankelIntegrand s ρ := by
  rw [integrand, kernel_eq_div_two_mul_I_mul_sin,
    slantCpow_ofReal_mul_exp_pi_div_four_mul_I hρ (-s),
    exp_pi_mul_I_mul_ofReal_mul_exp_pi_div_four_mul_I_sq,
    show ((π / 4 : ℝ) : ℂ) * I * (-s) = ((-(π / 4) : ℝ) : ℂ) * I * s by push_cast; ring,
    hankelIntegrand, mul_assoc ((π : ℂ)) ((ρ : ℂ))]
  field_simp
theorem integrand_neg_ofReal_mul_exp_pi_div_four_mul_I (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    integrand s (-((ρ : ℂ) * exp ((π / 4 : ℝ) * I)))
      = -(exp ((3 * π / 4 : ℝ) * I * s) / (2 * I)) * hankelIntegrand s ρ := by
  rw [integrand, slantCpow_neg_ofReal_mul_exp_pi_div_four_mul_I hρ (-s),
    show ((-(3 * π / 4) : ℝ) : ℂ) * I * (-s) = ((3 * π / 4 : ℝ) : ℂ) * I * s by push_cast; ring,
    kernel_neg, kernel_eq_div_two_mul_I_mul_sin,
    exp_pi_mul_I_mul_ofReal_mul_exp_pi_div_four_mul_I_sq, hankelIntegrand,
    mul_assoc ((π : ℂ)) ((ρ : ℂ))]
  field_simp
theorem contourIntegrand_zero_of_pos (s : ℂ) {w : ℝ} (hw : 0 < w) :
    contourIntegrand s 0 w
      = exp ((-(π / 4) : ℝ) * I * s) / (2 * I) * hankelIntegrand s (Real.sqrt 2 * w) := by
  rw [contourIntegrand, line_zero]
  exact integrand_ofReal_mul_exp_pi_div_four_mul_I s (mul_pos (Real.sqrt_pos.2 two_pos) hw)
theorem contourIntegrand_zero_of_neg (s : ℂ) {w : ℝ} (hw : w < 0) :
    contourIntegrand s 0 w
      = -(exp ((3 * π / 4 : ℝ) * I * s) / (2 * I)) * hankelIntegrand s (Real.sqrt 2 * -w) := by
  rw [contourIntegrand, line_zero,
    show ((Real.sqrt 2 * w : ℝ) : ℂ) = -(((Real.sqrt 2 * -w : ℝ)) : ℂ) by push_cast; ring, neg_mul]
  exact integrand_neg_ofReal_mul_exp_pi_div_four_mul_I s
    (mul_pos (Real.sqrt_pos.2 two_pos) (neg_pos.2 hw))
theorem integrableOn_hankelIntegrand_comp_mul_left {s : ℂ} (hs : s.re < 0) :
    IntegrableOn (fun w : ℝ ↦ hankelIntegrand s (Real.sqrt 2 * w)) (Set.Ioi (0 : ℝ)) :=
  (integrableOn_Ioi_comp_mul_left_iff (hankelIntegrand s) 0 (Real.sqrt_pos.2 two_pos)).2
    (by simpa using integrableOn_hankelIntegrand hs)
theorem integrableOn_contourIntegrand_zero_Ioi {s : ℂ} (hs : s.re < 0) :
    IntegrableOn (contourIntegrand s 0) (Set.Ioi (0 : ℝ)) :=
  IntegrableOn.congr_fun ((integrableOn_hankelIntegrand_comp_mul_left hs).const_mul _)
    (fun _ hw ↦ (contourIntegrand_zero_of_pos s hw).symm) measurableSet_Ioi
theorem integrableOn_contourIntegrand_zero_Iic {s : ℂ} (hs : s.re < 0) :
    IntegrableOn (contourIntegrand s 0) (Set.Iic (0 : ℝ)) := by
  have hneg : IntegrableOn (fun w : ℝ ↦ hankelIntegrand s (Real.sqrt 2 * -w))
      (Set.Iio (0 : ℝ)) := by
    simpa using (integrableOn_hankelIntegrand_comp_mul_left hs).comp_neg
  rw [integrableOn_Iic_iff_integrableOn_Iio]
  exact IntegrableOn.congr_fun (hneg.const_mul _)
    (fun w hw ↦ (contourIntegrand_zero_of_neg s hw).symm) measurableSet_Iio
theorem contourIntegral_zero_eq_neg_exp_mul_sin_mul_hankelIntegral {s : ℂ} (hs : s.re < 0) :
    contourIntegral s 0
      = -(exp ((π / 4 : ℝ) * I * (1 + s)) * sin ((π : ℂ) * s / 2)) * hankelIntegral s := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs2.ne'
  have hscale : ∀ c : ℂ, (∫ w in Set.Ioi (0 : ℝ), c * hankelIntegrand s (Real.sqrt 2 * w))
      = c * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * hankelIntegral s) := fun c ↦ by
    rw [integral_const_mul, integral_comp_mul_left_Ioi (hankelIntegrand s) 0 hs2, mul_zero,
      Complex.real_smul, hankelIntegral]
    push_cast
    ring
  have hIoi : (∫ w in Set.Ioi (0 : ℝ), contourIntegrand s 0 w)
      = exp ((-(π / 4) : ℝ) * I * s) / (2 * I) *
        (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * hankelIntegral s) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ contourIntegrand_zero_of_pos s hw]
    exact hscale _
  have hIic : (∫ w in Set.Iic (0 : ℝ), contourIntegrand s 0 w)
      = -(exp ((3 * π / 4 : ℝ) * I * s) / (2 * I)) *
        (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * hankelIntegral s) := by
    have hflip := integral_comp_neg_Ioi (0 : ℝ) (contourIntegrand s 0)
    rw [neg_zero] at hflip
    rw [← hflip, setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ by
      simpa only [neg_neg] using contourIntegrand_zero_of_neg s (neg_lt_zero.2 hw)]
    exact hscale _
  have hsum : exp ((-(π / 4) : ℝ) * I * s) / (2 * I) + -(exp ((3 * π / 4 : ℝ) * I * s) / (2 * I))
      = -(exp ((π / 4 : ℝ) * I * s) * sin ((π : ℂ) * s / 2)) := by
    rw [show ((-(π / 4) : ℝ) : ℂ) * I * s
        = ((π / 4 : ℝ) : ℂ) * I * s + -((π : ℂ) * s / 2 * I) by push_cast; ring,
      show ((3 * π / 4 : ℝ) : ℂ) * I * s
        = ((π / 4 : ℝ) : ℂ) * I * s + (π : ℂ) * s / 2 * I by push_cast; ring,
      exp_add, exp_add, ← sub_eq_add_neg, div_sub_div_same, ← mul_sub,
      div_eq_iff (by simp : (2 * I : ℂ) ≠ 0)]
    linear_combination (-exp (((π / 4 : ℝ) : ℂ) * I * s)) *
      Complex.exp_mul_I_sub_exp_neg_mul_I ((π : ℂ) * s / 2)
  have hrot : (1 + I) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = exp ((π / 4 : ℝ) * I) := by
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 :=
      mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    rw [inv_eq_one_div, mul_one_div, div_eq_iff hne, Complex.exp_pi_div_four_mul_I]
    push_cast
    linear_combination (-(1 : ℂ) / 2 - I / 2) * h2
  rw [contourIntegral, ← intervalIntegral.integral_Iic_add_Ioi
      (integrableOn_contourIntegrand_zero_Iic hs) (integrableOn_contourIntegrand_zero_Ioi hs),
    hIic, hIoi,
    show ((π / 4 : ℝ) : ℂ) * I * (1 + s) = ((π / 4 : ℝ) : ℂ) * I + ((π / 4 : ℝ) : ℂ) * I * s by
      ring, exp_add]
  linear_combination
    ((1 + I) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * hankelIntegral s) * hsum
      - (exp (((π / 4 : ℝ) : ℂ) * I * s) * sin ((π : ℂ) * s / 2) * hankelIntegral s) * hrot
end Zeta.RiemannSiegel
end
end CertificatePort123


section CertificatePort124
section
open Complex Filter MeasureTheory Topology
open scoped Real
namespace Zeta.RiemannSiegel
theorem contourIntegral_eq_contourIntegral_of_le_half (s : ℂ) {a b : ℝ} (hb0 : 0 < b)
    (hba : b ≤ a) (ha : a ≤ 1 / 2) : contourIntegral s a = contourIntegral s b := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have ha0 : 0 < a := hb0.trans_le hba
  have hβ0 : 0 < b / Real.sqrt 2 := div_pos hb0 hs2
  have hβα : b / Real.sqrt 2 ≤ a / Real.sqrt 2 := by gcongr
  have key : ∀ᶠ H : ℝ in atTop, RectangleIntegral (rotatedIntegrand s)
      (((b / Real.sqrt 2 : ℝ) : ℂ) - (H : ℂ) * I)
      (((a / Real.sqrt 2 : ℝ) : ℂ) + (H : ℂ) * I) = 0 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
    set z : ℂ := ((b / Real.sqrt 2 : ℝ) : ℂ) - (H : ℂ) * I with hzdef
    set w : ℂ := ((a / Real.sqrt 2 : ℝ) : ℂ) + (H : ℂ) * I with hwdef
    have hzre : z.re = b / Real.sqrt 2 := by rw [hzdef]; simp
    have hwre : w.re = a / Real.sqrt 2 := by rw [hwdef]; simp
    have hzw2 : z.im ≤ w.im := by rw [hzdef, hwdef]; simpa using (by linarith : -H ≤ H)
    refine HolomorphicOn.vanishesOnRectangle (U := Rectangle z w) (fun ζ hζ ↦ ?_) subset_rfl
    obtain ⟨hr1, hr2, -, -⟩ := (mem_Rect (by rw [hzre, hwre]; exact hβα) hzw2 ζ).1 hζ
    rw [hzre] at hr1; rw [hwre] at hr2
    refine (differentiableAt_rotatedIntegrand s (hβ0.trans_le hr1) fun k hk ↦ ?_)
      |>.differentiableWithinAt
    have hkre : (k : ℝ) / Real.sqrt 2 = ζ.re := by
      rw [hk, ← Complex.ofReal_intCast, re_exp_pi_div_four_mul_I_mul_ofReal]
    have hk1 : b ≤ (k : ℝ) := (div_le_div_iff_of_pos_right hs2).1 (by rw [hkre]; exact hr1)
    have hk2 : (k : ℝ) ≤ a := (div_le_div_iff_of_pos_right hs2).1 (by rw [hkre]; exact hr2)
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by exact_mod_cast hb0.trans_le hk1 : (0 : ℤ) < k)
    linarith
  have hlim := tendsto_RectangleIntegral_rotatedIntegrand s hβ0 hβα
    (integrable_contourIntegrand_of_le_half s ha0 ha)
    (integrable_contourIntegrand_of_le_half s hb0 (hba.trans ha))
  exact sub_eq_zero.1 (tendsto_nhds_unique hlim
    (Tendsto.congr' (by filter_upwards [key] with H hH using hH.symm) tendsto_const_nhds))
theorem norm_contourIntegrand_le_of_le_half {s : ℂ} (hs : s.re ≤ 0) {a : ℝ} (ha0 : 0 < a)
    (ha : a ≤ 1 / 2) {w : ℝ} (hw : w ≠ 0) :
    ‖contourIntegrand s a w‖
      ≤ Real.exp (3 * π * |s.im| / 4 + (-s.re + 1) / 2 + 1) *
          ((1 + |w| ^ (-s.re - 1)) *
            Real.exp (-(π * w ^ 2) + (2 * (-s.re) + 2 + π) * |w|)) := by
  have hpi := Real.pi_pos
  set p : ℝ := -s.re with hp
  have hp0 : (0 : ℝ) ≤ p := by rw [hp]; linarith
  have hw0 : (0 : ℝ) < |w| := abs_pos.2 hw
  have hxpos : (0 : ℝ) < ‖line a w‖ := norm_pos_iff.2 (line_ne_zero ha0.ne' w)
  have hwx : |w| ≤ ‖line a w‖ := by simpa using Complex.abs_im_le_norm (line a w)
  have hxub : ‖line a w‖ ≤ 1 / 2 + 2 * |w| := (norm_line_le ha0.le w).trans (by linarith)
  have hZ0 : (0 : ℝ) ≤ |w| ^ (p - 1) := Real.rpow_nonneg (abs_nonneg w) _
  have hG0 : (0 : ℝ) < Real.exp (-(2 * π * w ^ 2) + π * |w|) := Real.exp_pos _
  have hquot : Real.exp (-(2 * π * (a + w) * w)) / (2 * ‖sin (π * line a w)‖)
      ≤ (1 + 1 / (2 * ‖line a w‖)) * Real.exp (-(2 * π * w ^ 2) + π * |w|) := by
    have hnum : Real.exp (-(2 * π * (a + w) * w)) ≤ Real.exp (-(2 * π * w ^ 2) + π * |w|) :=
      Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_right ha (abs_nonneg w),
        mul_le_mul_of_nonneg_left (neg_le_abs w) ha0.le])
    have hden : 1 / (2 * ‖sin (π * line a w)‖) ≤ 1 + 1 / (2 * ‖line a w‖) := by
      have hmin := norm_sin_pi_mul_line_ge_min ha0.le ha w
      have hinv : (0 : ℝ) ≤ 1 / (2 * ‖line a w‖) := by positivity
      rcases min_cases (1 / 2 : ℝ) ‖line a w‖ with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] at hmin
      · linarith [one_div_le_one_div_of_le one_pos
          (by linarith : (1 : ℝ) ≤ 2 * ‖sin (π * line a w)‖)]
      · linarith [one_div_le_one_div_of_le (by linarith)
          (by linarith : 2 * ‖line a w‖ ≤ 2 * ‖sin (π * line a w)‖)]
    rw [div_eq_mul_one_div]
    exact (mul_le_mul hnum hden (by positivity) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  have hmodulus : ‖contourIntegrand s a w‖
      ≤ Real.exp (3 * π * |s.im| / 4) *
        ((‖line a w‖ ^ p + ‖line a w‖ ^ (p - 1) / 2) *
          Real.exp (-(2 * π * w ^ 2) + π * |w|)) := by
    have hrp : ‖line a w‖ ^ p * (1 + 1 / (2 * ‖line a w‖))
        = ‖line a w‖ ^ p + ‖line a w‖ ^ (p - 1) / 2 := by
      rw [Real.rpow_sub hxpos, Real.rpow_one]
      field_simp
    rw [norm_contourIntegrand_eq_exp s ha0, Real.exp_add, ← Real.rpow_def_of_pos hxpos,
      Complex.neg_re, ← hp]
    calc ‖line a w‖ ^ p * Real.exp (slantArg (line a w) * s.im) *
          (Real.exp (-(2 * π * (a + w) * w)) / (2 * ‖sin (π * line a w)‖))
        ≤ ‖line a w‖ ^ p * Real.exp (3 * π * |s.im| / 4) *
          ((1 + 1 / (2 * ‖line a w‖)) * Real.exp (-(2 * π * w ^ 2) + π * |w|)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 (slantArg_line_mul_im_le s ha0 w)) (Real.rpow_nonneg hxpos.le _))
            hquot (by positivity) (by positivity)
      _ = _ := by rw [← hrp]; ring
  have hE1 : (1 : ℝ) ≤ Real.exp ((p + 1) * (1 / 2 + 2 * |w|)) :=
    Real.one_le_exp (by nlinarith [abs_nonneg w])
  have hpow : ‖line a w‖ ^ p ≤ Real.exp ((p + 1) * (1 / 2 + 2 * |w|)) := by
    rw [Real.rpow_def_of_pos hxpos]
    exact Real.exp_le_exp.2 (by nlinarith [Real.log_le_sub_one_of_pos hxpos, abs_nonneg w])
  have hpowSub : ‖line a w‖ ^ (p - 1)
      ≤ |w| ^ (p - 1) + Real.exp ((p + 1) * (1 / 2 + 2 * |w|)) := by
    rcases le_or_gt 0 (p - 1) with hq | hq
    · have hpos : (0 : ℝ) < 1 / 2 + 2 * |w| := by positivity
      refine le_add_of_nonneg_of_le hZ0 ((Real.rpow_le_rpow hxpos.le hxub hq).trans ?_)
      rw [Real.rpow_def_of_pos hpos]
      exact Real.exp_le_exp.2 (by nlinarith [Real.log_le_sub_one_of_pos hpos, abs_nonneg w])
    · linarith [Real.rpow_le_rpow_of_nonpos hw0 hwx hq.le,
        (Real.exp_pos ((p + 1) * (1 / 2 + 2 * |w|))).le]
  have hbracket : ‖line a w‖ ^ p + ‖line a w‖ ^ (p - 1) / 2
      ≤ (1 + |w| ^ (p - 1)) * (3 / 2 * Real.exp ((p + 1) * (1 / 2 + 2 * |w|))) := by
    nlinarith [hpow, hpowSub, mul_nonneg hZ0 (sub_nonneg.2 hE1)]
  have he : (3 : ℝ) / 2 ≤ Real.exp (1 + π * w ^ 2) := by
    linarith [Real.add_one_le_exp (1 + π * w ^ 2), mul_nonneg hpi.le (sq_nonneg w)]
  have hgauss : 3 / 2 * (Real.exp ((p + 1) * (1 / 2 + 2 * |w|)) *
        Real.exp (-(2 * π * w ^ 2) + π * |w|))
      ≤ Real.exp ((p + 1) / 2 + 1) * Real.exp (-(π * w ^ 2) + (2 * p + 2 + π) * |w|) :=
    (mul_le_mul_of_nonneg_right he (by positivity)).trans_eq
      (by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring)
  rw [show 3 * π * |s.im| / 4 + (p + 1) / 2 + 1 = 3 * π * |s.im| / 4 + ((p + 1) / 2 + 1) by ring,
    Real.exp_add, mul_assoc]
  refine hmodulus.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  calc (‖line a w‖ ^ p + ‖line a w‖ ^ (p - 1) / 2) * Real.exp (-(2 * π * w ^ 2) + π * |w|)
      ≤ (1 + |w| ^ (p - 1)) * (3 / 2 * (Real.exp ((p + 1) * (1 / 2 + 2 * |w|)) *
          Real.exp (-(2 * π * w ^ 2) + π * |w|))) := by
        nlinarith [mul_le_mul_of_nonneg_right hbracket hG0.le]
    _ ≤ (1 + |w| ^ (p - 1)) * (Real.exp ((p + 1) / 2 + 1) *
          Real.exp (-(π * w ^ 2) + (2 * p + 2 + π) * |w|)) :=
        mul_le_mul_of_nonneg_left hgauss (by positivity)
    _ = _ := by ring
theorem contourIntegral_zero_eq_contourIntegral_half {s : ℂ} (hs : s.re < 0) :
    contourIntegral s 0 = contourIntegral s (1 / 2) := by
  let α : ℕ → ℝ := fun n ↦ 1 / 2 * (1 / ((n : ℝ) + 1))
  have hα0 : ∀ n, 0 < α n := fun n ↦ by positivity
  have hαle : ∀ n, α n ≤ 1 / 2 := fun n ↦ by
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; simp
    simpa [α] using mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hαtend : Tendsto α atTop (𝓝 0) := by
    simpa [α] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ)
  have hne : ∀ᵐ w : ℝ, w ≠ 0 := by rw [ae_iff]; simp
  have hgint : Integrable fun w : ℝ ↦
      Real.exp (3 * π * |s.im| / 4 + (-s.re + 1) / 2 + 1) *
        ((1 + |w| ^ (-s.re - 1)) *
          Real.exp (-(π * w ^ 2) + (2 * (-s.re) + 2 + π) * |w|)) := by
    have h1 := integrable_exp_neg_pi_mul_sq_add_mul_abs (2 * (-s.re) + 2 + π)
    have h2 := integrable_rpow_abs_mul_exp_neg_pi_mul_sq_add_mul_abs
      (q := -s.re - 1) (by linarith) (2 * (-s.re) + 2 + π)
    refine ((h1.add h2).const_mul
      (Real.exp (3 * π * |s.im| / 4 + (-s.re + 1) / 2 + 1))).congr
      (Filter.Eventually.of_forall fun w ↦ ?_)
    simp only [Pi.add_apply]
    ring
  have hlim : Tendsto (fun n : ℕ ↦ ∫ w : ℝ, contourIntegrand s (α n) w) atTop
      (𝓝 (∫ w : ℝ, contourIntegrand s 0 w)) := by
    refine tendsto_integral_of_dominated_convergence _
      (fun n ↦ (integrable_contourIntegrand_of_le_half s (hα0 n) (hαle n)).aestronglyMeasurable)
      hgint (fun n ↦ ?_) ?_
    · filter_upwards [hne] with w hw using
        norm_contourIntegrand_le_of_le_half hs.le (hα0 n) (hαle n) hw
    · filter_upwards [hne] with w hw
      have hslit : exp ((π / 4 : ℝ) * I) * line 0 w ∈ slitPlane := by
        refine mem_slitPlane_iff.2 (Or.inr ?_)
        rw [exp_pi_div_four_mul_I_mul_line]
        simpa using mul_ne_zero (Real.sqrt_pos.2 two_pos).ne' hw
      have hnotInt : ∀ k : ℤ, line 0 w ≠ (k : ℂ) := fun k hk ↦
        hw (by simpa [line_im] using congrArg Complex.im hk)
      have hcont : ContinuousAt (integrand s) (line 0 w) :=
        (differentiableAt_integrand s hslit hnotInt).continuousAt
      have hline : Tendsto (fun n : ℕ ↦ line (α n) w) atTop (𝓝 (line 0 w)) :=
        ((by unfold line; fun_prop : Continuous fun t : ℝ ↦ line t w).tendsto 0).comp hαtend
      exact hcont.tendsto.comp hline
  have h1 : Tendsto (fun n : ℕ ↦ contourIntegral s (α n)) atTop (𝓝 (contourIntegral s 0)) := by
    simpa only [contourIntegral] using hlim.const_mul _
  refine tendsto_nhds_unique h1 (Tendsto.congr' ?_ tendsto_const_nhds)
  filter_upwards with n using
    contourIntegral_eq_contourIntegral_of_le_half s (hα0 n) (hαle n) le_rfl
theorem contourIntegral_half_eq_neg_exp_mul_sin_mul_hankelIntegral {s : ℂ} (hs : s.re < 0) :
    contourIntegral s (1 / 2)
      = -(exp ((π / 4 : ℝ) * I * (1 + s)) * sin ((π : ℂ) * s / 2)) * hankelIntegral s := by
  rw [← contourIntegral_zero_eq_contourIntegral_half hs]
  exact contourIntegral_zero_eq_neg_exp_mul_sin_mul_hankelIntegral hs
end Zeta.RiemannSiegel
end
end CertificatePort124


section CertificatePort125
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def mirrorContourIntegral (s : ℂ) (a : ℝ) : ℂ :=
  starRingEnd ℂ (contourIntegral (starRingEnd ℂ s) a)
noncomputable def mirrorHankelIntegrand (s : ℂ) (ρ : ℝ) : ℂ :=
  (ρ : ℂ) ^ (-s) * exp (-(π * (ρ : ℂ) ^ 2)) / sin (π * ρ * exp (-((π / 4 : ℝ) * I)))
noncomputable def mirrorHankelIntegral (s : ℂ) : ℂ :=
  starRingEnd ℂ (hankelIntegral (starRingEnd ℂ s))
theorem mirrorHankelIntegrand_eq_conj (s : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    mirrorHankelIntegrand s ρ = starRingEnd ℂ (hankelIntegrand (starRingEnd ℂ s) ρ) := by
  have hcpow : ((ρ : ℂ)) ^ (-s) = starRingEnd ℂ ((ρ : ℂ) ^ (-(starRingEnd ℂ s))) := by
    simpa [Complex.conj_ofReal] using Complex.conj_cpow (ρ : ℂ) (-s)
      (by rw [Complex.arg_ofReal_of_nonneg hρ]; exact fun h ↦ Real.pi_ne_zero h.symm)
  have hexp : exp (-((π : ℂ) * (ρ : ℂ) ^ 2))
      = starRingEnd ℂ (exp (-((π : ℂ) * (ρ : ℂ) ^ 2))) := by
    rw [← Complex.exp_conj]; simp
  have hsin : sin ((π : ℂ) * ρ * exp (-((π / 4 : ℝ) * I)))
      = starRingEnd ℂ (sin ((π : ℂ) * ρ * exp ((π / 4 : ℝ) * I))) := by
    rw [← Complex.sin_conj, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
      ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  rw [mirrorHankelIntegrand, hankelIntegrand, map_div₀, map_mul, ← hcpow, ← hexp, ← hsin]
theorem integrableOn_mirrorHankelIntegrand {s : ℂ} (hs : s.re < 0) :
    IntegrableOn (mirrorHankelIntegrand s) (Set.Ioi (0 : ℝ)) := by
  have h := integrableOn_hankelIntegrand (s := starRingEnd ℂ s) (by simpa using hs)
  have heq : ∀ ρ ∈ Set.Ioi (0 : ℝ),
      mirrorHankelIntegrand s ρ = starRingEnd ℂ (hankelIntegrand (starRingEnd ℂ s) ρ) :=
    fun ρ hρ ↦ mirrorHankelIntegrand_eq_conj s (le_of_lt hρ)
  refine Integrable.mono' h.norm ?_ ?_
  · refine (Complex.continuous_conj.comp_aestronglyMeasurable h.aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ using (heq ρ hρ).symm
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ using
      (heq ρ hρ ▸ (Complex.norm_conj _)).le
theorem mirrorHankelIntegral_eq_integral (s : ℂ) :
    mirrorHankelIntegral s = ∫ ρ in Set.Ioi (0 : ℝ), mirrorHankelIntegrand s ρ := by
  rw [mirrorHankelIntegral, hankelIntegral, ← integral_conj]
  exact setIntegral_congr_fun measurableSet_Ioi fun ρ hρ ↦
    (mirrorHankelIntegrand_eq_conj s (le_of_lt hρ)).symm
theorem mirrorContourIntegral_one_sub_eq {s : ℂ} (hs : 1 < s.re) :
    mirrorContourIntegral (1 - s) (1 / 2)
      = -(exp (-((π / 4 : ℝ) * I * (2 - s))) * cos ((π : ℂ) * s / 2)) *
          mirrorHankelIntegral (1 - s) := by
  have hz : ((1 : ℂ) - (starRingEnd ℂ) s).re < 0 := by
    simp only [sub_re, one_re, conj_re]
    linarith
  have hexp : (starRingEnd ℂ) (exp ((π / 4 : ℝ) * I * (1 + ((1 : ℂ) - (starRingEnd ℂ) s))))
      = exp (-((π / 4 : ℝ) * I * (2 - s))) := by
    rw [← exp_conj]
    congr 1
    simp only [map_mul, map_add, map_one, map_sub, conj_conj, conj_I, conj_ofReal]
    ring
  have hsin : (starRingEnd ℂ) (sin ((π : ℂ) * ((1 : ℂ) - (starRingEnd ℂ) s) / 2))
      = cos ((π : ℂ) * s / 2) := by
    rw [← sin_conj, show (starRingEnd ℂ) ((π : ℂ) * ((1 : ℂ) - (starRingEnd ℂ) s) / 2)
        = (π : ℂ) / 2 - (π : ℂ) * s / 2 by
      simp only [map_div₀, map_mul, map_sub, map_one, conj_conj, conj_ofReal, map_ofNat]
      ring]
    exact sin_pi_div_two_sub _
  rw [mirrorContourIntegral, mirrorHankelIntegral, map_sub, map_one,
    contourIntegral_half_eq_neg_exp_mul_sin_mul_hankelIntegral hz, map_mul, map_neg, map_mul,
    hexp, hsin]
end Zeta.RiemannSiegel
end
end CertificatePort125


section CertificatePort126
section
open Complex Filter MeasureTheory Topology
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def mordellIntegrand (u x : ℂ) : ℂ :=
  exp (-(2 * π * I * u * x)) * kernel x
noncomputable def mordellIntegral (u : ℂ) (a : ℝ) : ℂ :=
  slantIntegral (mordellIntegrand u) a
noncomputable def rotatedMordellIntegrand (u : ℂ) : ℂ → ℂ := rotatedFun (mordellIntegrand u)
theorem rotatedMordellIntegrand_exp_mul (u x : ℂ) :
    rotatedMordellIntegrand u (exp ((π / 4 : ℝ) * I) * x)
      = exp (-((π / 4 : ℝ) * I)) * mordellIntegrand u x :=
  rotatedFun_exp_mul _ _
theorem differentiableAt_mordellIntegrand (u : ℂ) {x : ℂ} (hx : ∀ n : ℤ, x ≠ n) :
    DifferentiableAt ℂ (mordellIntegrand u) x := by
  unfold mordellIntegrand
  exact (by fun_prop : DifferentiableAt ℂ (fun x : ℂ ↦ exp (-(2 * π * I * u * x))) x).mul
    (differentiableAt_kernel hx)
theorem differentiableAt_rotatedMordellIntegrand (u : ℂ) {z : ℂ}
    (hz : ∀ n : ℤ, z ≠ exp ((π / 4 : ℝ) * I) * n) :
    DifferentiableAt ℂ (rotatedMordellIntegrand u) z :=
  differentiableAt_rotatedFun (differentiableAt_mordellIntegrand u fun n hcon ↦ hz n (by
    rw [← hcon, ← mul_assoc, exp_pi_div_four_mul_I_mul_exp_neg, one_mul]))
theorem tendsto_sub_mul_mordellIntegrand (u : ℂ) (n : ℤ) :
    Tendsto (fun x ↦ (x - n) * mordellIntegrand u x) (𝓝[≠] (n : ℂ))
      (𝓝 (exp (-(2 * π * I * u * n)) / (2 * π * I))) := by
  rw [div_eq_mul_one_div]
  refine Tendsto.congr (fun x ↦ ?_)
    ((((by fun_prop : Continuous fun x : ℂ ↦ exp (-(2 * π * I * u * x))).tendsto
      (n : ℂ)).mono_left nhdsWithin_le_nhds).mul (tendsto_sub_mul_kernel n))
  rw [mordellIntegrand]; ring
theorem tendsto_sub_mul_rotatedMordellIntegrand (u : ℂ) (n : ℤ) :
    Tendsto (fun z ↦ (z - exp ((π / 4 : ℝ) * I) * n) * rotatedMordellIntegrand u z)
      (𝓝[≠] (exp ((π / 4 : ℝ) * I) * n)) (𝓝 (exp (-(2 * π * I * u * n)) / (2 * π * I))) :=
  tendsto_sub_mul_rotatedFun (tendsto_sub_mul_mordellIntegrand u n)
theorem norm_mordellIntegrand_le (u : ℂ) {x : ℂ} (hx : Real.sqrt 2 / 2 ≤ |x.im|) :
    ‖mordellIntegrand u x‖ ≤ Real.exp (2 * π * ‖u‖ * ‖x‖ - 2 * π * x.re * x.im) := by
  have hsin : (1 : ℝ) ≤ ‖sin ((π : ℂ) * x)‖ := Complex.one_le_norm_sin_pi_mul hx
  have hnorm : ‖mordellIntegrand u x‖
      = ‖exp (-(2 * π * I * u * x))‖ *
        (Real.exp (-(2 * π * x.re * x.im)) / (2 * ‖sin (π * x)‖)) := by
    rw [mordellIntegrand, norm_mul, kernel_eq_div_two_mul_I_mul_sin, norm_div,
      Complex.norm_exp_pi_mul_I_mul_sq,
      show ‖(2 : ℂ) * I * sin ((π : ℂ) * x)‖ = 2 * ‖sin ((π : ℂ) * x)‖ by simp]
  have hexp : ‖exp (-(2 * π * I * u * x))‖ ≤ Real.exp (2 * π * ‖u‖ * ‖x‖) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_)
    rw [norm_neg]
    simp [abs_of_pos Real.pi_pos, mul_assoc]
  rw [hnorm, show 2 * π * ‖u‖ * ‖x‖ - 2 * π * x.re * x.im
      = 2 * π * ‖u‖ * ‖x‖ + -(2 * π * x.re * x.im) by ring, Real.exp_add]
  exact mul_le_mul hexp (div_le_self (Real.exp_pos _).le (by linarith)) (by positivity)
    (Real.exp_pos _).le
private theorem norm_rotatedMordellIntegrand_le (u : ℂ) {ξ y : ℝ} (hξ : 0 ≤ ξ) (h2 : 1 ≤ |y - ξ|) :
    ‖rotatedMordellIntegrand u ((ξ : ℂ) + (y : ℂ) * I)‖
      ≤ Real.exp (2 * π * ‖u‖ * (ξ + |y|) + π * ξ ^ 2 - π * |y| ^ 2) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2n : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  set x : ℂ := exp (-((π / 4 : ℝ) * I)) * ((ξ : ℂ) + (y : ℂ) * I) with hxdef
  have hxre : x.re = Real.sqrt 2 / 2 * (ξ + y) := by
    rw [hxdef, exp_neg_pi_div_four_mul_I_mul_re]; simp
  have hxim : x.im = Real.sqrt 2 / 2 * (y - ξ) := by
    rw [hxdef, exp_neg_pi_div_four_mul_I_mul_im]; simp
  have hnx : ‖x‖ = ‖(ξ : ℂ) + (y : ℂ) * I‖ := by
    rw [hxdef, norm_mul, norm_exp_neg_pi_div_four_mul_I, one_mul]
  have hnx2 : ‖x‖ ≤ ξ + |y| := by
    rw [hnx]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp [abs_of_nonneg hξ]
  have hxim2 := le_abs_im_of_im_eq_mul (by positivity) hxim h2
  have hbound := norm_mordellIntegrand_le u hxim2
  refine le_trans ?_ (hbound.trans (Real.exp_le_exp.2 ?_))
  · rw [rotatedMordellIntegrand, norm_rotatedFun, ← hxdef]
  · have hprod : 2 * π * x.re * x.im = π * |y| ^ 2 - π * ξ ^ 2 := by
      rw [hxre, hxim, sq_abs]
      linear_combination (π * (y ^ 2 - ξ ^ 2) / 2) * hs2
    rw [hprod]
    have := mul_le_mul_of_nonneg_left hnx2 (by positivity : (0 : ℝ) ≤ 2 * π * ‖u‖)
    linarith
theorem tendsto_HIntegral_rotatedMordellIntegrand (u : ℂ) {β α : ℝ} (hβ : 0 < β) (hβα : β ≤ α)
    {y : ℝ → ℝ} (hy : Tendsto (fun H ↦ |y H|) atTop atTop) :
    Tendsto (fun H ↦ HIntegral (rotatedMordellIntegrand u) β α (y H)) atTop (𝓝 0) := by
  refine tendsto_HIntegral_of_norm_le (C₀ := 2 * π * ‖u‖ * α + π * α ^ 2) (C₁ := 2 * π * ‖u‖)
    (T := α + 1) hβα Real.pi_pos (fun ξ v hξ1 hξ2 hv ↦ ?_) hy
  have hξ0 : 0 < ξ := hβ.trans_le hξ1
  have h2 : 1 ≤ |v - ξ| := by
    linarith [abs_sub_abs_le_abs_sub v ξ, abs_of_nonneg hξ0.le]
  refine (norm_rotatedMordellIntegrand_le u hξ0.le h2).trans (Real.exp_le_exp.2 ?_)
  have hsq : ξ ^ 2 ≤ α ^ 2 := by nlinarith
  rw [sq_abs]
  nlinarith [mul_le_mul_of_nonneg_left hξ2 (by positivity : (0 : ℝ) ≤ 2 * π * ‖u‖),
    mul_le_mul_of_nonneg_left hsq Real.pi_pos.le]
private theorem neg_mul_line_add_mul_line_sq (u : ℂ) (a w : ℝ) :
    -(2 * π * I * u * line a w) + π * I * line a w ^ 2
      = (-2 * π : ℂ) * (w : ℂ) ^ 2 + 2 * π * I * (1 + I) * ((a : ℂ) - u) * (w : ℂ)
        + (π * I * (a : ℂ) ^ 2 - 2 * π * I * u * (a : ℂ)) := by
  simp only [line, Complex.ofReal_add]
  linear_combination ((π : ℂ) * (w : ℂ) ^ 2 * (I + 2)) * Complex.I_sq
theorem mordellIntegrand_line (u : ℂ) (a w : ℝ) :
    mordellIntegrand u (line a w)
      = exp ((-2 * π : ℂ) * (w : ℂ) ^ 2 + 2 * π * I * (1 + I) * ((a : ℂ) - u) * (w : ℂ)
          + (π * I * (a : ℂ) ^ 2 - 2 * π * I * u * (a : ℂ))) / (2 * I * sin (π * line a w)) := by
  rw [mordellIntegrand, kernel_eq_div_two_mul_I_mul_sin, ← mul_div_assoc, ← Complex.exp_add,
    neg_mul_line_add_mul_line_sq u a w]
theorem integrable_mordellIntegrand {a : ℝ} {n : ℤ} (ha : a = n + 1 / 2) (u : ℂ) :
    Integrable fun w : ℝ ↦ mordellIntegrand u (line a w) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hb : (-2 * π : ℂ).re < 0 := by simpa using Real.pi_pos
  have hline := continuous_line a
  have hcont : Continuous fun w : ℝ ↦ mordellIntegrand u (line a w) := by
    have hker : Continuous fun w : ℝ ↦ kernel (line a w) := by
      simp only [kernel_eq_div_two_mul_I_mul_sin]
      exact Continuous.div (by fun_prop) (by fun_prop) fun w ↦ by
        simpa [I_ne_zero] using sin_pi_mul_line_ne_zero ha w
    simp only [mordellIntegrand]
    exact (((continuous_const.mul hline).neg).cexp).mul hker
  refine Integrable.mono' (((integrable_cexp_quadratic' hb
    (2 * π * I * (1 + I) * ((a : ℂ) - u))
    (π * I * (a : ℂ) ^ 2 - 2 * π * I * u * (a : ℂ))).norm).div_const (Real.sqrt 2))
    hcont.aestronglyMeasurable (.of_forall fun w ↦ ?_)
  rw [mordellIntegrand_line u a w, norm_div,
    show ‖(2 : ℂ) * I * sin ((π : ℂ) * line a w)‖ = 2 * ‖sin ((π : ℂ) * line a w)‖ by simp]
  gcongr
  linarith [norm_sin_pi_mul_line_ge ha w]
theorem mordellIntegrand_sub_mordellIntegrand_add_one (u : ℂ) {x : ℂ} (hx : ∀ n : ℤ, x ≠ n) :
    mordellIntegrand u x - mordellIntegrand (u + 1) x
      = exp (-(π * I * (u + 1 / 2) ^ 2)) * exp (π * I * (x - (u + 1 / 2)) ^ 2) := by
  have hs : sin ((π : ℂ) * x) ≠ 0 := Complex.sin_pi_mul_ne_zero hx
  have hden : (2 : ℂ) * I * sin (π * x) ≠ 0 := by simpa [I_ne_zero] using hs
  have hnum : (1 : ℂ) - exp (-(2 * π * I * x)) = exp (-(π * I * x)) * (2 * I * sin (π * x)) := by
    rw [show (2 : ℂ) * I * sin (π * x) = exp (π * I * x) - exp (-(π * I * x)) from by
        rw [show ((π : ℂ) * I * x) = ((π : ℂ) * x) * I by ring]
        exact (exp_mul_I_sub_exp_neg_mul_I _).symm,
      mul_sub, ← Complex.exp_add, ← Complex.exp_add,
      show -((π : ℂ) * I * x) + π * I * x = 0 by ring, Complex.exp_zero,
      show -((π : ℂ) * I * x) + -(π * I * x) = -(2 * π * I * x) by ring]
  have hL : mordellIntegrand u x - mordellIntegrand (u + 1) x
      = exp (-(2 * π * I * u * x)) * exp (π * I * x ^ 2) * (1 - exp (-(2 * π * I * x))) /
        (2 * I * sin (π * x)) := by
    rw [mordellIntegrand, mordellIntegrand, kernel_eq_div_two_mul_I_mul_sin,
      show -(2 * (π : ℂ) * I * (u + 1) * x) = -(2 * π * I * u * x) + -(2 * π * I * x) by ring,
      Complex.exp_add]
    field_simp
  rw [hL, hnum, ← mul_assoc, mul_div_assoc, div_self hden, mul_one, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring
theorem mordellIntegral_sub_mordellIntegral_add_one {a : ℝ} {n : ℤ} (ha : a = n + 1 / 2) (u : ℂ) :
    mordellIntegral u a - mordellIntegral (u + 1) a
      = exp ((π / 4 : ℝ) * I) * exp (-(π * I * (u + 1 / 2) ^ 2)) := by
  have hpt : ∀ w : ℝ, mordellIntegrand u (line a w) - mordellIntegrand (u + 1) (line a w)
      = exp (-(π * I * (u + 1 / 2) ^ 2)) * exp (π * I * (line a w - (u + 1 / 2)) ^ 2) := fun w ↦
    mordellIntegrand_sub_mordellIntegrand_add_one u fun k hk ↦
      sin_pi_mul_line_ne_zero ha w (by rw [hk, mul_comm]; exact Complex.sin_int_mul_pi k)
  have hint : ∫ w : ℝ, (mordellIntegrand u (line a w) - mordellIntegrand (u + 1) (line a w))
      = exp (-(π * I * (u + 1 / 2) ^ 2)) *
        ∫ w : ℝ, exp (π * I * (line a w - (u + 1 / 2)) ^ 2) := by
    rw [MeasureTheory.integral_congr_ae (.of_forall hpt), MeasureTheory.integral_const_mul]
  rw [mordellIntegral, mordellIntegral, slantIntegral, slantIntegral, ← mul_sub,
    ← MeasureTheory.integral_sub (integrable_mordellIntegrand ha u)
      (integrable_mordellIntegrand ha (u + 1)), hint]
  linear_combination exp (-(π * I * (u + 1 / 2) ^ 2)) *
    integral_exp_pi_mul_I_mul_line_sub_sq a (u + 1 / 2)
theorem mordellIntegrand_add_one (u x : ℂ) :
    mordellIntegrand u (x + 1) = exp (-(2 * π * I * u)) * mordellIntegrand (u - 1) x := by
  rw [mordellIntegrand, mordellIntegrand, kernel_add_one,
    show exp (-(2 * (π : ℂ) * I * u * (x + 1))) * (exp (2 * π * I * x) * kernel x)
      = (exp (-(2 * (π : ℂ) * I * u * (x + 1))) * exp (2 * π * I * x)) * kernel x by ring,
    show exp (-(2 * (π : ℂ) * I * u)) * (exp (-(2 * π * I * (u - 1) * x)) * kernel x)
      = (exp (-(2 * (π : ℂ) * I * u)) * exp (-(2 * π * I * (u - 1) * x))) * kernel x by ring,
    ← Complex.exp_add, ← Complex.exp_add,
    show -(2 * (π : ℂ) * I * u * (x + 1)) + 2 * π * I * x
      = -(2 * (π : ℂ) * I * u) + -(2 * π * I * (u - 1) * x) by ring]
theorem mordellIntegral_add_one (u : ℂ) (a : ℝ) :
    mordellIntegral u (a + 1) = exp (-(2 * π * I * u)) * mordellIntegral (u - 1) a := by
  simp only [mordellIntegral, slantIntegral, line_add_one, mordellIntegrand_add_one]
  rw [MeasureTheory.integral_const_mul]
  ring
theorem mordellIntegral_sub_exp_mul_mordellIntegral_add_one (u : ℂ) :
    mordellIntegral u (1 / 2) - exp (2 * π * I * u) * mordellIntegral (u + 1) (1 / 2) = 1 := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have key : ∀ v : ℂ, exp (-(2 * π * I * v)) * mordellIntegral (v - 1) (1 / 2)
      - mordellIntegral v (1 / 2) = exp (-(2 * π * I * v)) := by
    intro v
    have hres : 2 * (π : ℂ) * I * (exp (-(2 * π * I * v * (1 : ℤ))) / (2 * π * I))
        = exp (-(2 * π * I * v)) := by
      have hpiC : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
      push_cast
      field_simp
    have hβ : (0 : ℝ) < (((1 : ℤ) : ℝ) - 1 / 2) / Real.sqrt 2 := by
      push_cast; positivity
    have hβα : (((1 : ℤ) : ℝ) - 1 / 2) / Real.sqrt 2 ≤ (((1 : ℤ) : ℝ) + 1 / 2) / Real.sqrt 2 := by
      rw [div_le_div_iff_of_pos_right hs2]; norm_num
    have hpole := slantIntegral_sub_slantIntegral_of_pole (f := mordellIntegrand v)
      (F := rotatedMordellIntegrand v) (n := 1)
      (R := exp (-(2 * π * I * v * (1 : ℤ))) / (2 * π * I)) one_pos
      (rotatedMordellIntegrand_exp_mul v)
      (fun z _ hz ↦ differentiableAt_rotatedMordellIntegrand v hz)
      (tendsto_sub_mul_rotatedMordellIntegrand v 1)
      (tendsto_HIntegral_rotatedMordellIntegrand v hβ hβα
        (by simpa using tendsto_abs_atTop_atTop))
      (tendsto_HIntegral_rotatedMordellIntegrand v hβ hβα tendsto_abs_atTop_atTop)
      (integrable_mordellIntegrand (n := 1) rfl v)
      (integrable_mordellIntegrand (n := 0) (by push_cast; ring) v)
    rw [hres] at hpole
    have h32 : (((1 : ℤ) : ℝ) + 1 / 2) = 1 / 2 + 1 := by push_cast; ring
    have h12 : (((1 : ℤ) : ℝ) - 1 / 2) = 1 / 2 := by push_cast; ring
    rw [h32, h12] at hpole
    rw [← mordellIntegral_add_one v (1 / 2)]
    simpa [mordellIntegral] using hpole
  have h := key (u + 1)
  rw [add_sub_cancel_right] at h
  have he : exp (-(2 * (π : ℂ) * I * (u + 1))) = exp (-(2 * π * I * u)) := by
    rw [show -(2 * (π : ℂ) * I * (u + 1)) = -(2 * π * I * u) + ((-1 : ℤ) : ℂ) * (2 * π * I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [he] at h
  have hinv : exp (2 * (π : ℂ) * I * u) * exp (-(2 * π * I * u)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination exp (2 * (π : ℂ) * I * u) * h -
    (mordellIntegral u (1 / 2) - 1) * hinv
theorem mordellIntegral_eq {u : ℂ} (hu : ∀ n : ℤ, u ≠ n) :
    mordellIntegral u (1 / 2)
      = (exp (-(π * I * u ^ 2)) - exp (-(π * I * u))) /
        (exp (π * I * u) - exp (-(π * I * u))) := by
  have hden : exp ((π : ℂ) * I * u) - exp (-((π : ℂ) * I * u)) ≠ 0 := by
    rw [show ((π : ℂ) * I * u) = ((π : ℂ) * u) * I by ring, exp_mul_I_sub_exp_neg_mul_I]
    simpa [I_ne_zero] using Complex.sin_pi_mul_ne_zero hu
  have hR : exp ((π / 4 : ℝ) * I) * exp (-((π : ℂ) * I * (u + 1 / 2) ^ 2))
      = exp (-((π : ℂ) * I * u ^ 2)) * exp (-((π : ℂ) * I * u)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  have hP : exp (2 * (π : ℂ) * I * u) = exp ((π : ℂ) * I * u) * exp ((π : ℂ) * I * u) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hinv : exp ((π : ℂ) * I * u) * exp (-((π : ℂ) * I * u)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hg := mordellIntegral_sub_mordellIntegral_add_one (a := 1 / 2) (n := 0) (by norm_num) u
  have hp := mordellIntegral_sub_exp_mul_mordellIntegral_add_one u
  rw [hR] at hg
  rw [hP] at hp
  have hB : mordellIntegral (u + 1) (1 / 2)
      = mordellIntegral u (1 / 2) - exp (-((π : ℂ) * I * u ^ 2)) * exp (-((π : ℂ) * I * u)) := by
    linear_combination -hg
  rw [hB] at hp
  rw [eq_div_iff hden]
  linear_combination (-exp (-((π : ℂ) * I * u))) * hp +
    (exp ((π : ℂ) * I * u) * exp (-((π : ℂ) * I * u ^ 2)) * exp (-((π : ℂ) * I * u))
      - exp ((π : ℂ) * I * u) * mordellIntegral u (1 / 2)
      + exp (-((π : ℂ) * I * u ^ 2))) * hinv
end Zeta.RiemannSiegel
end
end CertificatePort126


section CertificatePort127
section
open Complex MeasureTheory Set
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def rayIntegrand (f : ℂ → ℂ) (s : ℂ) (ρ : ℝ) : ℂ :=
  ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) ^ (-s) * f ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I)))
noncomputable def rayIntegral (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  exp (-((π / 4 : ℝ) * I)) * ∫ ρ in Ioi (0 : ℝ), rayIntegrand f s ρ
theorem conj_exp_pi_div_four_mul_I_mul_ofReal (ρ : ℝ) :
    starRingEnd ℂ (exp ((π / 4 : ℝ) * I) * (ρ : ℂ)) = (ρ : ℂ) * exp (-((π / 4 : ℝ) * I)) := by
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, mul_neg, mul_comm]
theorem re_ofReal_mul_exp_neg_pi_div_four_mul_I (ρ : ℝ) :
    ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))).re = ρ / Real.sqrt 2 := by
  rw [← conj_exp_pi_div_four_mul_I_mul_ofReal, Complex.conj_re,
    re_exp_pi_div_four_mul_I_mul_ofReal]
theorem im_ofReal_mul_exp_neg_pi_div_four_mul_I (ρ : ℝ) :
    ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))).im = -(ρ / Real.sqrt 2) := by
  rw [mul_comm, Complex.exp_neg_pi_div_four_mul_I_mul_im, Complex.ofReal_im, Complex.ofReal_re,
    Real.sqrt_div_self']
  ring
theorem ofReal_mul_exp_neg_pi_div_four_mul_I_ne_intCast {ρ : ℝ} (hρ : 0 < ρ) (n : ℤ) :
    (ρ : ℂ) * exp (-((π / 4 : ℝ) * I)) ≠ (n : ℂ) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  intro h
  have him := im_ofReal_mul_exp_neg_pi_div_four_mul_I ρ
  rw [h, Complex.intCast_im] at him
  have : 0 < ρ / Real.sqrt 2 := div_pos hρ h2
  linarith
theorem ofReal_mul_exp_neg_pi_div_four_mul_I_mem_slitPlane {ρ : ℝ} (hρ : 0 < ρ) :
    (ρ : ℂ) * exp (-((π / 4 : ℝ) * I)) ∈ slitPlane :=
  mem_slitPlane_iff.2 (Or.inl (by
    rw [re_ofReal_mul_exp_neg_pi_div_four_mul_I]
    exact div_pos hρ (Real.sqrt_pos.2 two_pos)))
theorem rayIntegrand_eq (f : ℂ → ℂ) (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    rayIntegrand f s ρ
      = (ρ : ℂ) ^ (-s) * exp ((π / 4 : ℝ) * I * s) * f ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) := by
  have hpi := Real.pi_pos
  have hcpow : ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) ^ (-s)
      = (ρ : ℂ) ^ (-s) * exp ((π / 4 : ℝ) * I * s) := by
    rw [show -(((π / 4 : ℝ) : ℂ) * I) = ((-(π / 4) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.ofReal_mul_exp_mul_I_cpow hρ (by linarith) (by linarith) (-s),
      show ((-(π / 4) : ℝ) : ℂ) * I * (-s) = ((π / 4 : ℝ) : ℂ) * I * s by push_cast; ring]
  rw [rayIntegrand, hcpow]
theorem norm_rayIntegrand (f : ℂ → ℂ) (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ‖rayIntegrand f s ρ‖
      = ρ ^ (-s.re) * Real.exp (-(π / 4 * s.im)) *
          ‖f ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I)))‖ := by
  rw [rayIntegrand_eq f s hρ, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hρ,
    Complex.norm_exp, Complex.neg_re,
    show (((π / 4 : ℝ) : ℂ) * I * s).re = -(π / 4 * s.im) by
      simp [Complex.mul_re, Complex.mul_im]]
theorem rayIntegral_congr {f g : ℂ → ℂ} {s : ℂ}
    (h : ∀ ρ : ℝ, 0 < ρ → f ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I)))
      = g ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I)))) :
    rayIntegral f s = rayIntegral g s := by
  rw [rayIntegral, rayIntegral]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun ρ hρ ↦ by
    rw [rayIntegrand, rayIntegrand, h ρ hρ]
theorem rayIntegral_add {f g : ℂ → ℂ} {s : ℂ} (hf : IntegrableOn (rayIntegrand f s) (Ioi 0))
    (hg : IntegrableOn (rayIntegrand g s) (Ioi 0)) :
    rayIntegral (fun u ↦ f u + g u) s = rayIntegral f s + rayIntegral g s := by
  rw [rayIntegral, rayIntegral, rayIntegral, ← mul_add, ← integral_add hf hg]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun ρ _ ↦ by
    rw [rayIntegrand, rayIntegrand, rayIntegrand, mul_add]
private theorem rayIntegrand_exp_eq (s z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    rayIntegrand (fun u ↦ exp (-(2 * π * I * u * z))) s ρ
      = exp ((π / 4 : ℝ) * I * s) *
          ((ρ : ℂ) ^ (-s) * exp (-(((2 * π : ℝ) : ℂ) * (exp ((π / 4 : ℝ) * I) * z) * ρ))) := by
  rw [rayIntegrand_eq _ s hρ,
    show -(2 * (π : ℂ) * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) * z)
      = -(((2 * π : ℝ) : ℂ) * (exp ((π / 4 : ℝ) * I) * z) * ρ) by
      rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
      linear_combination (-(2 * (π : ℂ) * (ρ : ℂ) * z)) *
        Complex.I_mul_exp_neg_pi_div_four_mul_I]
  ring
private theorem norm_rayIntegrand_exp (s z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ‖rayIntegrand (fun u ↦ exp (-(2 * π * I * u * z))) s ρ‖
      = Real.exp (-(π / 4 * s.im)) *
          (ρ ^ (-s.re) * Real.exp (-(2 * π * (exp ((π / 4 : ℝ) * I) * z).re * ρ))) := by
  rw [rayIntegrand_exp_eq s z hρ, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
    Complex.norm_cpow_eq_rpow_re_of_pos hρ, Complex.neg_re,
    show (((π / 4 : ℝ) : ℂ) * I * s).re = -(π / 4 * s.im) by
      simp [Complex.mul_re, Complex.mul_im],
    show (-(((2 * π : ℝ) : ℂ) * (exp ((π / 4 : ℝ) * I) * z) * (ρ : ℂ))).re
      = -(2 * π * (exp ((π / 4 : ℝ) * I) * z).re * ρ) by
      rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, Complex.re_ofReal_mul]]
private theorem re_ofReal_two_pi_mul_pos {z : ℂ} (hz : 0 < (exp ((π / 4 : ℝ) * I) * z).re) :
    0 < (((2 * π : ℝ) : ℂ) * (exp ((π / 4 : ℝ) * I) * z)).re := by
  rw [Complex.re_ofReal_mul]
  exact mul_pos (by positivity) hz
theorem integrableOn_rayIntegrand_exp_neg_two_pi_mul_I_mul {s z : ℂ} (hs : s.re < 1)
    (hz : 0 < (exp ((π / 4 : ℝ) * I) * z).re) :
    IntegrableOn (rayIntegrand (fun u ↦ exp (-(2 * π * I * u * z))) s) (Ioi 0) := by
  have ha : 0 < (1 - s).re := by simpa using hs
  have hb := re_ofReal_two_pi_mul_pos hz
  refine IntegrableOn.congr_fun ((Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi ha hb).const_mul
    (exp ((π / 4 : ℝ) * I * s))) (fun ρ hρ ↦ ?_) measurableSet_Ioi
  rw [rayIntegrand_exp_eq s z hρ, show (1 : ℂ) - s - 1 = -s by ring]
theorem rayIntegral_exp_neg_two_pi_mul_I_mul {s z : ℂ} (hs : s.re < 1)
    (hz : 0 < (exp ((π / 4 : ℝ) * I) * z).re) :
    rayIntegral (fun u ↦ exp (-(2 * π * I * u * z))) s
      = ((2 * π : ℝ) : ℂ) ^ (s - 1) * exp ((π / 2 : ℝ) * I * (s - 1)) * Gamma (1 - s) *
          slantCpow z (s - 1) := by
  have hz0 : exp ((π / 4 : ℝ) * I) * z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hb := re_ofReal_two_pi_mul_pos hz
  have hint : ∫ ρ in Ioi (0 : ℝ), rayIntegrand (fun u ↦ exp (-(2 * π * I * u * z))) s ρ
      = exp ((π / 4 : ℝ) * I * s) *
          (Gamma (1 - s) * (((2 * π : ℝ) : ℂ) * (exp ((π / 4 : ℝ) * I) * z)) ^ (s - 1)) := by
    rw [← Complex.integral_cpow_neg_mul_exp_neg_mul_Ioi hs hb, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun ρ hρ ↦ rayIntegrand_exp_eq s z hρ
  have hph : exp (-((π / 4 : ℝ) * I)) * exp ((π / 4 : ℝ) * I * s)
      = exp ((π / 2 : ℝ) * I * (s - 1)) * exp (-((π / 4 : ℝ) * I * (s - 1))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [rayIntegral, hint, Complex.ofReal_mul_cpow (by positivity) hz0, slantCpow]
  linear_combination (Gamma (1 - s) * ((2 * π : ℝ) : ℂ) ^ (s - 1) *
    (exp ((π / 4 : ℝ) * I) * z) ^ (s - 1)) * hph
private theorem one_sub_exp_two_pi_mul_I_mul_eq (u : ℂ) :
    1 - exp (2 * π * I * u) = -(exp (π * I * u) * (2 * I * sin (π * u))) := by
  rw [show (2 : ℂ) * I * sin ((π : ℂ) * u) = exp ((π : ℂ) * u * I) - exp (-((π : ℂ) * u * I)) from
    (Complex.exp_mul_I_sub_exp_neg_mul_I _).symm, mul_sub, ← Complex.exp_add, ← Complex.exp_add]
  rw [show (π : ℂ) * I * u + (π : ℂ) * u * I = 2 * π * I * u by ring,
    show (π : ℂ) * I * u + -((π : ℂ) * u * I) = 0 by ring, Complex.exp_zero]
  ring
private theorem le_norm_one_sub_exp_ray {ρ : ℝ} (hρ : 0 < ρ) :
    Real.sqrt 2 * π * ρ * Real.exp (π * ρ / Real.sqrt 2)
      ≤ ‖1 - exp (2 * π * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))))‖ := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hpi := Real.pi_pos
  set u : ℂ := (ρ : ℂ) * exp (-((π / 4 : ℝ) * I)) with hu
  have him : ((π : ℂ) * u).im = -(π * ρ / Real.sqrt 2) := by
    rw [show (π : ℂ) * u = ((π : ℝ) : ℂ) * u by norm_cast, Complex.im_ofReal_mul, hu,
      im_ofReal_mul_exp_neg_pi_div_four_mul_I]
    ring
  have hexp : ‖exp ((π : ℂ) * I * u)‖ = Real.exp (π * ρ / Real.sqrt 2) := by
    rw [Complex.norm_exp, show ((π : ℂ) * I * u).re = -((π : ℂ) * u).im by
      simp [Complex.mul_re, Complex.mul_im], him, neg_neg]
  have hsin : π * ρ / Real.sqrt 2 ≤ ‖sin ((π : ℂ) * u)‖ := by
    refine le_trans (Real.self_le_sinh_iff.2 (by positivity)) ?_
    have h := Complex.sinh_abs_im_le_norm_sin ((π : ℂ) * u)
    rwa [him, abs_neg, abs_of_nonneg (by positivity)] at h
  have hval : 2 * (π * ρ / Real.sqrt 2) = Real.sqrt 2 * π * ρ := by
    rw [show 2 * (π * ρ / Real.sqrt 2) = 2 / Real.sqrt 2 * (π * ρ) by ring, Real.div_sqrt]; ring
  rw [one_sub_exp_two_pi_mul_I_mul_eq, norm_neg, norm_mul, hexp,
    show ‖(2 : ℂ) * I * sin ((π : ℂ) * u)‖ = 2 * ‖sin ((π : ℂ) * u)‖ by simp, ← hval]
  have := mul_le_mul_of_nonneg_left hsin (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [Real.exp_pos (π * ρ / Real.sqrt 2)]
private theorem norm_rayIntegrand_inv_one_sub_exp_le (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ‖rayIntegrand (fun u ↦ (1 - exp (2 * π * I * u))⁻¹) s ρ‖
      ≤ Real.exp (-(π / 4 * s.im)) / (Real.sqrt 2 * π) *
          (ρ ^ (-s.re - 1) * Real.exp (-(π / Real.sqrt 2) * ρ)) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hpi := Real.pi_pos
  have hlb := le_norm_one_sub_exp_ray hρ
  rw [norm_rayIntegrand _ s hρ, norm_inv]
  calc ρ ^ (-s.re) * Real.exp (-(π / 4 * s.im)) *
        ‖1 - exp (2 * π * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))))‖⁻¹
      ≤ ρ ^ (-s.re) * Real.exp (-(π / 4 * s.im)) *
        (Real.sqrt 2 * π * ρ * Real.exp (π * ρ / Real.sqrt 2))⁻¹ := by gcongr
    _ = Real.exp (-(π / 4 * s.im)) / (Real.sqrt 2 * π) *
        (ρ ^ (-s.re - 1) * Real.exp (-(π / Real.sqrt 2) * ρ)) := by
        rw [Real.rpow_sub hρ, Real.rpow_one, mul_inv, mul_inv,
          show -(π / Real.sqrt 2) * ρ = -(π * ρ / Real.sqrt 2) by ring,
          Real.exp_neg (π * ρ / Real.sqrt 2), div_eq_mul_inv, div_eq_mul_inv]
        ring
theorem integrableOn_rayIntegrand_inv_one_sub_exp {s : ℂ} (hs : s.re < 0) :
    IntegrableOn (rayIntegrand (fun u ↦ (1 - exp (2 * π * I * u))⁻¹) s) (Ioi 0) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hmaj : IntegrableOn (fun ρ : ℝ ↦ Real.exp (-(π / 4 * s.im)) / (Real.sqrt 2 * π) *
      (ρ ^ (-s.re - 1) * Real.exp (-(π / Real.sqrt 2) * ρ))) (Ioi 0) :=
    (Real.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) (by positivity)).const_mul _
  have hmeas : AEStronglyMeasurable
      (rayIntegrand (fun u ↦ (1 - exp (2 * π * I * u))⁻¹) s) (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (ContinuousOn.cpow (by fun_prop) continuousOn_const fun ρ hρ ↦ ?_)
      (ContinuousOn.inv₀ (by fun_prop) fun ρ hρ ↦ ?_)
    · exact ofReal_mul_exp_neg_pi_div_four_mul_I_mem_slitPlane hρ
    · have hρ0 : (0 : ℝ) < ρ := hρ
      exact norm_pos_iff.1 (lt_of_lt_of_le (by positivity) (le_norm_one_sub_exp_ray hρ0))
  refine Integrable.mono' hmaj hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ using
    norm_rayIntegrand_inv_one_sub_exp_le s hρ
private theorem tsum_rayIntegrand_exp (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∑' n : ℕ, rayIntegrand (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s ρ
      = -rayIntegrand (fun u ↦ (1 - exp (2 * π * I * u))⁻¹) s ρ := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  set x : ℂ := (ρ : ℂ) * exp (-((π / 4 : ℝ) * I)) with hxdef
  have hq : ‖exp (-(2 * (π : ℂ) * I * x))‖ < 1 := by
    rw [Complex.norm_exp,
      show (-(2 * (π : ℂ) * I * x)).re = 2 * π * x.im by simp [Complex.mul_re, Complex.mul_im],
      Real.exp_lt_one_iff, hxdef, im_ofReal_mul_exp_neg_pi_div_four_mul_I]
    nlinarith [Real.pi_pos, div_pos hρ h2]
  have hqne : exp (-(2 * (π : ℂ) * I * x)) ≠ 0 := Complex.exp_ne_zero _
  have hq0 : (1 : ℂ) - exp (-(2 * (π : ℂ) * I * x)) ≠ 0 :=
    sub_ne_zero_of_ne fun h ↦ by rw [← h] at hq; simp at hq
  have hterm : ∀ n : ℕ, rayIntegrand (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s ρ
      = x ^ (-s) * exp (-(2 * (π : ℂ) * I * x)) * exp (-(2 * (π : ℂ) * I * x)) ^ n := fun n ↦ by
    have h : exp (-(2 * (π : ℂ) * I * x)) * exp (-(2 * (π : ℂ) * I * x)) ^ n
        = exp (-(2 * (π : ℂ) * I * x * ((n : ℂ) + 1))) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      ring
    rw [rayIntegrand, ← hxdef, ← h, ← mul_assoc]
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_norm_lt_one hq, rayIntegrand, ← hxdef,
    show exp (2 * (π : ℂ) * I * x) = (exp (-(2 * (π : ℂ) * I * x)))⁻¹ by
      rw [← Complex.exp_neg]; ring_nf,
    show (1 : ℂ) - (exp (-(2 * (π : ℂ) * I * x)))⁻¹
      = -((1 - exp (-(2 * (π : ℂ) * I * x))) * (exp (-(2 * (π : ℂ) * I * x)))⁻¹) by
      field_simp; ring, inv_neg, mul_inv, inv_inv]
  ring
theorem rayIntegral_inv_one_sub_exp {s : ℂ} (hs : s.re < 0) :
    rayIntegral (fun u ↦ (1 - exp (2 * π * I * u))⁻¹) s
      = -(((2 * π : ℝ) : ℂ) ^ (s - 1) * exp ((π / 2 : ℝ) * I * (s - 1)) * Gamma (1 - s) *
          riemannZeta (1 - s)) := by
  have hs1 : s.re < 1 := by linarith
  set C : ℂ := ((2 * π : ℝ) : ℂ) ^ (s - 1) * exp ((π / 2 : ℝ) * I * (s - 1)) * Gamma (1 - s)
    with hC
  have hzre : ∀ n : ℕ, 0 < (exp ((π / 4 : ℝ) * I) * ((n : ℂ) + 1)).re := fun n ↦ by
    rw [show ((n : ℂ) + 1) = ((((n : ℝ) + 1 : ℝ)) : ℂ) by push_cast; ring,
      re_exp_pi_div_four_mul_I_mul_ofReal]
    positivity
  have hval : ∀ n : ℕ, rayIntegral (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s
      = C * (((n : ℂ) + 1) ^ (s - 1)) := fun n ↦ by
    rw [rayIntegral_exp_neg_two_pi_mul_I_mul hs1 (hzre n),
      show ((n : ℂ) + 1) = ((((n : ℝ) + 1 : ℝ)) : ℂ) by push_cast; ring,
      slantCpow_ofReal (by positivity), hC]
  have h1 : 1 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hfe : ∀ n : ℕ, ((n : ℂ) + 1) ^ (s - 1) = 1 / ((n : ℂ) + 1) ^ (1 - s) := fun n ↦ by
    rw [one_div, ← Complex.cpow_neg, neg_sub]
  have hzeta : HasSum (fun n : ℕ ↦ ((n : ℂ) + 1) ^ (s - 1)) (riemannZeta (1 - s)) := by
    have hsum : Summable fun n : ℕ ↦ ((n : ℂ) + 1) ^ (s - 1) :=
      ((summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 h1)).congr fun n ↦ by
        rw [hfe]
        push_cast
        ring_nf
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow h1, ← tsum_congr hfe]
    exact hsum.hasSum
  have hInt : ∀ n : ℕ, IntegrableOn
      (rayIntegrand (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s) (Ioi 0) :=
    fun n ↦ integrableOn_rayIntegrand_exp_neg_two_pi_mul_I_mul hs1 (hzre n)
  have hnorm : ∀ (n : ℕ) (ρ : ℝ), 0 < ρ →
      ‖rayIntegrand (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s ρ‖
        = Real.exp (-(π / 4 * s.im)) *
            (ρ ^ (-s.re) * Real.exp (-(Real.sqrt 2 * π * ((n : ℝ) + 1) * ρ))) := fun n ρ hρ ↦ by
    rw [norm_rayIntegrand_exp s _ hρ,
      show ((n : ℂ) + 1) = ((((n : ℝ) + 1 : ℝ)) : ℂ) by push_cast; ring,
      re_exp_pi_div_four_mul_I_mul_ofReal,
      show 2 * π * (((n : ℝ) + 1) / Real.sqrt 2) * ρ
        = 2 / Real.sqrt 2 * (π * ((n : ℝ) + 1) * ρ) by ring, Real.div_sqrt]
    ring_nf
  have hSum : Summable fun n : ℕ ↦
      ∫ ρ in Ioi (0 : ℝ), ‖rayIntegrand (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s ρ‖ := by
    have hval2 : ∀ n : ℕ,
        (∫ ρ in Ioi (0 : ℝ),
          ‖rayIntegrand (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s ρ‖)
          = Real.exp (-(π / 4 * s.im)) * (Real.Gamma (1 - s.re) *
              ((Real.sqrt 2 * π) ^ (s.re - 1) * ((n : ℝ) + 1) ^ (s.re - 1))) := fun n ↦ by
      rw [setIntegral_congr_fun measurableSet_Ioi (fun ρ hρ ↦ hnorm n ρ hρ), integral_const_mul,
        Real.integral_rpow_neg_mul_exp_neg_mul_Ioi hs1 (by positivity),
        Real.mul_rpow (by positivity) (by positivity)]
    refine Summable.congr ?_ fun n ↦ (hval2 n).symm
    have hbase : Summable fun n : ℕ ↦ ((n : ℝ) + 1) ^ (s.re - 1) :=
      Summable.congr ((summable_nat_add_iff 1).2
        (Real.summable_nat_rpow.mpr (by linarith : s.re - 1 < -1))) fun n ↦ by push_cast; ring
    exact ((hbase.mul_left _).mul_left _).mul_left _
  have hleft : (exp (-((π / 4 : ℝ) * I)) *
      ∫ ρ in Ioi (0 : ℝ), ∑' n : ℕ, rayIntegrand
        (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s ρ)
      = -rayIntegral (fun u ↦ (1 - exp (2 * π * I * u))⁻¹) s := by
    rw [rayIntegral, ← mul_neg (exp (-((π / 4 : ℝ) * I))), ← integral_neg]
    exact congrArg _
      (setIntegral_congr_fun measurableSet_Ioi fun ρ hρ ↦ tsum_rayIntegrand_exp s hρ)
  have hHS : HasSum (fun n : ℕ ↦ rayIntegral
      (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s)
      (-rayIntegral (fun u ↦ (1 - exp (2 * π * I * u))⁻¹) s) := by
    have h := (hasSum_integral_of_summable_integral_norm
      (μ := volume.restrict (Ioi (0 : ℝ))) hInt hSum).mul_left (exp (-((π / 4 : ℝ) * I)))
    rwa [hleft] at h
  have hfin : HasSum (fun n : ℕ ↦ rayIntegral
      (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s) (C * riemannZeta (1 - s)) := by
    simpa only [hval] using hzeta.mul_left C
  linear_combination -(hHS.unique hfin)
private theorem rayIntegrand_mirrorKernel_eq (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    rayIntegrand (fun u ↦ exp (-(π * I * u ^ 2)) / (exp (π * I * u) - exp (-(π * I * u)))) s ρ
      = exp ((π / 4 : ℝ) * I * s) / (2 * I) * mirrorHankelIntegrand s ρ := by
  have hgauss : exp (-((π : ℂ) * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) ^ 2))
      = exp (-((π : ℂ) * (ρ : ℂ) ^ 2)) := by
    congr 1
    linear_combination (-(π : ℂ) * I * (ρ : ℂ) ^ 2) * Complex.exp_neg_pi_div_four_mul_I_mul_self +
      ((π : ℂ) * (ρ : ℂ) ^ 2) * Complex.I_sq
  have hden : exp ((π : ℂ) * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))))
        - exp (-((π : ℂ) * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I)))))
      = 2 * I * sin ((π : ℂ) * (ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) := by
    rw [show (π : ℂ) * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I)))
        = (π : ℂ) * (ρ : ℂ) * exp (-((π / 4 : ℝ) * I)) * I by ring]
    exact Complex.exp_mul_I_sub_exp_neg_mul_I _
  rw [rayIntegrand_eq _ s hρ, hgauss, hden, mirrorHankelIntegrand]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring
theorem integrableOn_rayIntegrand_mirrorKernel {s : ℂ} (hs : s.re < 0) :
    IntegrableOn (rayIntegrand
      (fun u ↦ exp (-(π * I * u ^ 2)) / (exp (π * I * u) - exp (-(π * I * u)))) s) (Ioi 0) :=
  IntegrableOn.congr_fun ((integrableOn_mirrorHankelIntegrand hs).const_mul
    (exp ((π / 4 : ℝ) * I * s) / (2 * I)))
    (fun _ hρ ↦ (rayIntegrand_mirrorKernel_eq s hρ).symm) measurableSet_Ioi
theorem rayIntegral_mirrorKernel (s : ℂ) :
    rayIntegral (fun u ↦ exp (-(π * I * u ^ 2)) / (exp (π * I * u) - exp (-(π * I * u)))) s
      = exp ((π / 4 : ℝ) * I * (s - 1)) / (2 * I) * mirrorHankelIntegral s := by
  have hph : exp ((π / 4 : ℝ) * I * (s - 1))
      = exp (-((π / 4 : ℝ) * I)) * exp ((π / 4 : ℝ) * I * s) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [rayIntegral, setIntegral_congr_fun measurableSet_Ioi
      (fun ρ hρ ↦ rayIntegrand_mirrorKernel_eq s hρ),
    integral_const_mul, ← mirrorHankelIntegral_eq_integral, hph]
  ring
private noncomputable def contourRayIntegrand (s : ℂ) (ρ w : ℝ) : ℂ :=
  rayIntegrand (fun u ↦ exp (-(2 * π * I * u * line (1 / 2) w))) s ρ * kernel (line (1 / 2) w)
private theorem norm_contourRayIntegrand_le (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (w : ℝ) :
    ‖contourRayIntegrand s ρ w‖
      ≤ Real.exp (-(π / 4 * s.im)) * (ρ ^ (-s.re) * Real.exp (-(π / Real.sqrt 2) * ρ)) *
        (Real.exp (π / 4) * Real.sqrt 2 * Real.exp (-(π * w ^ 2))) := by
  have hconst : Real.exp (π / 4) / (Real.sqrt 2 * ((1 : ℝ) / 2))
      = Real.exp (π / 4) * Real.sqrt 2 := by
    rw [eq_comm, eq_div_iff (by positivity)]
    nlinarith [Real.exp_pos (π / 4), Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hk := norm_kernel_line_le (a := (1 : ℝ) / 2) (by norm_num) le_rfl w
  rw [show π * ((1 : ℝ) / 2) ^ 2 = π / 4 by ring, hconst] at hk
  rw [contourRayIntegrand, norm_mul, norm_rayIntegrand_exp s _ hρ,
    re_exp_pi_div_four_mul_I_mul_line,
    show -(2 * π * ((1 / 2 : ℝ) / Real.sqrt 2) * ρ) = -(π / Real.sqrt 2) * ρ by ring]
  exact mul_le_mul_of_nonneg_left hk
    (mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.rpow_nonneg hρ.le _) (Real.exp_pos _).le))
private theorem continuousOn_uncurry_contourRayIntegrand (s : ℂ) :
    ContinuousOn (Function.uncurry (contourRayIntegrand s))
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
  have hlinew : Continuous (line (1 / 2)) := continuous_line (1 / 2)
  have hline : Continuous fun z : ℝ × ℝ ↦ line (1 / 2) z.2 := hlinew.comp continuous_snd
  have hpt : Continuous fun z : ℝ × ℝ ↦ ((z.1 : ℂ) * exp (-((π / 4 : ℝ) * I))) := by fun_prop
  have hker : Continuous fun w : ℝ ↦ kernel (line (1 / 2) w) := by
    simp only [kernel_eq_div_two_mul_I_mul_sin]
    exact Continuous.div (by fun_prop) (by fun_prop) fun w ↦ by
      simpa [Complex.I_ne_zero] using
        sin_pi_mul_line_ne_zero (a := (1 : ℝ) / 2) (n := 0) (by norm_num) w
  change ContinuousOn (fun z : ℝ × ℝ ↦ (((z.1 : ℂ) * exp (-((π / 4 : ℝ) * I))) ^ (-s) *
      exp (-(2 * π * I * ((z.1 : ℂ) * exp (-((π / 4 : ℝ) * I))) * line (1 / 2) z.2)))
      * kernel (line (1 / 2) z.2)) _
  refine ContinuousOn.mul (ContinuousOn.mul
    (ContinuousOn.cpow hpt.continuousOn continuousOn_const fun z hz ↦ ?_)
    (Complex.continuous_exp.comp (((continuous_const.mul hpt).mul hline).neg)).continuousOn)
    (hker.comp continuous_snd).continuousOn
  exact ofReal_mul_exp_neg_pi_div_four_mul_I_mem_slitPlane hz.1
theorem rayIntegral_mordellIntegral {s : ℂ} (hs : s.re < 0) :
    rayIntegral (fun u ↦ mordellIntegral u (1 / 2)) s
      = ((2 * π : ℝ) : ℂ) ^ (s - 1) * exp ((π / 2 : ℝ) * I * (s - 1)) * Gamma (1 - s) *
          contourIntegral (1 - s) (1 / 2) := by
  have hpi := Real.pi_pos
  have hs1 : s.re < 1 := by linarith
  have hfub : Integrable (Function.uncurry (contourRayIntegrand s))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    have hAint : IntegrableOn (fun ρ : ℝ ↦ Real.exp (-(π / 4 * s.im)) *
        (ρ ^ (-s.re) * Real.exp (-(π / Real.sqrt 2) * ρ))) (Ioi 0) :=
      (Real.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) (by positivity)).const_mul _
    have hBint : Integrable fun w : ℝ ↦
        Real.exp (π / 4) * Real.sqrt 2 * Real.exp (-(π * w ^ 2)) := by
      simpa [neg_mul] using
        (integrable_exp_neg_mul_sq hpi).const_mul (Real.exp (π / 4) * Real.sqrt 2)
    refine Integrable.mono' (hAint.mul_prod hBint) ?_ ?_
    · rw [Measure.restrict_prod_eq_prod_univ]
      exact (continuousOn_uncurry_contourRayIntegrand s).aestronglyMeasurable
        (measurableSet_Ioi.prod MeasurableSet.univ)
    · rw [Measure.restrict_prod_eq_prod_univ]
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with z hz
      exact norm_contourRayIntegrand_le s hz.1 z.2
  have hrow : ∀ ρ : ℝ, rayIntegrand (fun u ↦ mordellIntegral u (1 / 2)) s ρ
      = (1 + I) * ∫ w : ℝ, contourRayIntegrand s ρ w := fun ρ ↦ by
    have heq : ∀ w : ℝ, contourRayIntegrand s ρ w
        = ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) ^ (-s) *
            mordellIntegrand ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) (line (1 / 2) w) := fun w ↦ by
      rw [contourRayIntegrand, rayIntegrand, mordellIntegrand]
      ring
    rw [integral_congr_ae (.of_forall heq), integral_const_mul, rayIntegrand, mordellIntegral,
      slantIntegral]
    ring
  have hcol : ∀ w : ℝ, exp (-((π / 4 : ℝ) * I)) * ∫ ρ in Ioi (0 : ℝ), contourRayIntegrand s ρ w
      = ((2 * π : ℝ) : ℂ) ^ (s - 1) * exp ((π / 2 : ℝ) * I * (s - 1)) * Gamma (1 - s) *
          contourIntegrand (1 - s) (1 / 2) w := fun w ↦ by
    have hzre : 0 < (exp ((π / 4 : ℝ) * I) * line (1 / 2) w).re := by
      rw [re_exp_pi_div_four_mul_I_mul_line]
      positivity
    rw [show (∫ ρ in Ioi (0 : ℝ), contourRayIntegrand s ρ w)
        = (∫ ρ in Ioi (0 : ℝ), rayIntegrand
            (fun u ↦ exp (-(2 * π * I * u * line (1 / 2) w))) s ρ) * kernel (line (1 / 2) w) from
      integral_mul_const _ _, ← mul_assoc, ← rayIntegral,
      rayIntegral_exp_neg_two_pi_mul_I_mul hs1 hzre, contourIntegrand, integrand,
      show -(1 - s) = s - 1 by ring]
    ring
  rw [rayIntegral, setIntegral_congr_fun measurableSet_Ioi (fun ρ _ ↦ hrow ρ),
    integral_const_mul, integral_integral_swap hfub,
    show exp (-((π / 4 : ℝ) * I)) *
        ((1 + I) * ∫ w : ℝ, ∫ ρ in Ioi (0 : ℝ), contourRayIntegrand s ρ w)
      = (1 + I) * (exp (-((π / 4 : ℝ) * I)) *
          ∫ w : ℝ, ∫ ρ in Ioi (0 : ℝ), contourRayIntegrand s ρ w) by ring,
    ← integral_const_mul, integral_congr_ae (.of_forall hcol), integral_const_mul,
    contourIntegral]
  ring
private theorem mordellIntegral_ray_eq {ρ : ℝ} (hρ : 0 < ρ) :
    mordellIntegral ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) (1 / 2)
      = (1 - exp (2 * π * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I)))))⁻¹
        + exp (-(π * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) ^ 2)) /
            (exp (π * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))))
              - exp (-(π * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))))))  := by
  set u : ℂ := (ρ : ℂ) * exp (-((π / 4 : ℝ) * I))
  have hun : ∀ n : ℤ, u ≠ (n : ℂ) := ofReal_mul_exp_neg_pi_div_four_mul_I_ne_intCast hρ
  have hE : exp ((π : ℂ) * I * u) ≠ 0 := Complex.exp_ne_zero _
  have hsin : exp ((π : ℂ) * I * u) - exp (-((π : ℂ) * I * u)) = 2 * I * sin ((π : ℂ) * u) := by
    rw [show (π : ℂ) * I * u = (π : ℂ) * u * I by ring]
    exact Complex.exp_mul_I_sub_exp_neg_mul_I _
  have hD : exp ((π : ℂ) * I * u) - exp (-((π : ℂ) * I * u)) ≠ 0 := by
    rw [hsin]
    simpa [Complex.I_ne_zero] using Complex.sin_pi_mul_ne_zero hun
  have hone : (1 : ℂ) - exp (2 * (π : ℂ) * I * u)
      = -(exp ((π : ℂ) * I * u) * (exp ((π : ℂ) * I * u) - exp (-((π : ℂ) * I * u)))) := by
    rw [hsin, one_sub_exp_two_pi_mul_I_mul_eq]
  have hinv : exp ((π : ℂ) * I * u) * exp (-((π : ℂ) * I * u)) = 1 := by
    rw [← Complex.exp_add, show (π : ℂ) * I * u + -((π : ℂ) * I * u) = 0 by ring, Complex.exp_zero]
  rw [mordellIntegral_eq hun, hone]
  field_simp
  linear_combination -hinv
theorem riemannZeta_add_contourIntegral_half_eq {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s + contourIntegral s (1 / 2)
      = ((2 * π : ℝ) : ℂ) ^ s * exp (-((π / 4 : ℝ) * I * (2 - s))) / (2 * Gamma s) *
          mirrorHankelIntegral (1 - s) := by
  have ht : (1 - s).re < 0 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have h2π : ((2 * π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  have hΓ : Gamma s ≠ 0 := Complex.Gamma_ne_zero fun m h ↦ by
    rw [h] at hs
    simp only [Complex.neg_re, Complex.natCast_re] at hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hPQ : ((2 * π : ℝ) : ℂ) ^ ((1 - s) - 1) * ((2 * π : ℝ) : ℂ) ^ s = 1 := by
    rw [← Complex.cpow_add _ _ h2π, show (1 - s) - 1 + s = 0 by ring, Complex.cpow_zero]
  have hsplit : rayIntegral (fun u ↦ mordellIntegral u (1 / 2)) (1 - s)
      = rayIntegral (fun u ↦ (1 - exp (2 * π * I * u))⁻¹) (1 - s)
        + rayIntegral (fun u ↦ exp (-(π * I * u ^ 2)) /
            (exp (π * I * u) - exp (-(π * I * u)))) (1 - s) := by
    rw [← rayIntegral_add (integrableOn_rayIntegrand_inv_one_sub_exp ht)
      (integrableOn_rayIntegrand_mirrorKernel ht)]
    exact rayIntegral_congr fun ρ hρ ↦ mordellIntegral_ray_eq hρ
  rw [rayIntegral_mordellIntegral ht, rayIntegral_inv_one_sub_exp ht,
    rayIntegral_mirrorKernel (1 - s), show (1 : ℂ) - (1 - s) = s by ring] at hsplit
  have hph : I * exp ((π / 2 : ℝ) * I * ((1 - s) - 1)) * exp (-((π / 4 : ℝ) * I * (2 - s)))
      = exp ((π / 4 : ℝ) * I * ((1 - s) - 1)) := by
    rw [mul_assoc, ← Complex.exp_add,
      show ((π / 2 : ℝ) : ℂ) * I * ((1 - s) - 1) + -(((π / 4 : ℝ) : ℂ) * I * (2 - s))
        = -((π : ℂ) / 2 * I) + ((π / 4 : ℝ) : ℂ) * I * ((1 - s) - 1) by push_cast; ring,
      Complex.exp_add, ← mul_assoc, Complex.exp_neg, Complex.exp_pi_div_two_mul_I,
      mul_inv_cancel₀ Complex.I_ne_zero, one_mul]
  have hfrac : exp ((π / 4 : ℝ) * I * ((1 - s) - 1)) / (2 * I)
      = exp ((π / 2 : ℝ) * I * ((1 - s) - 1)) * exp (-((π / 4 : ℝ) * I * (2 - s))) / 2 := by
    rw [← hph]
    field_simp
  have hPne : ((2 * π : ℝ) : ℂ) ^ ((1 - s) - 1) ≠ 0 := by simp [Complex.cpow_eq_zero_iff]
  set P : ℂ := ((2 * π : ℝ) : ℂ) ^ ((1 - s) - 1)
  set Q : ℂ := ((2 * π : ℝ) : ℂ) ^ s
  set E : ℂ := exp ((π / 2 : ℝ) * I * ((1 - s) - 1))
  set F : ℂ := exp (-((π / 4 : ℝ) * I * (2 - s)))
  refine mul_left_cancel₀ (a := P * E * Gamma s)
    (mul_ne_zero (mul_ne_zero hPne (Complex.exp_ne_zero _)) hΓ) ?_
  rw [mul_add, hsplit, hfrac]
  field_simp
  linear_combination (-(E * F * mirrorHankelIntegral (1 - s))) * hPQ
end Zeta.RiemannSiegel
end
end CertificatePort127


section CertificatePort128
section
open Complex Filter
open scoped Real Topology
namespace Zeta.RiemannSiegel
theorem differentiable_mirrorContourIntegral_one_sub {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    Differentiable ℂ fun s ↦ mirrorContourIntegral (1 - s) a := fun s ↦ by
  rw [show (fun s : ℂ ↦ mirrorContourIntegral (1 - s) a)
      = starRingEnd ℂ ∘ (fun u : ℂ ↦ contourIntegral (1 - u) a) ∘ starRingEnd ℂ from
    funext fun u ↦ by simp [mirrorContourIntegral]]
  exact differentiableAt_conj_conj_iff.2
    ((differentiable_contourIntegral_of_le_half ha0 ha _).fun_comp' _
      ((differentiableAt_const 1).sub differentiableAt_fun_id))
theorem riemannZeta_add_contourIntegral_add_chi_mul_mirror_eq_zero_of_one_lt {s : ℂ}
    (hs : 1 < s.re) (hodd : ∀ n : ℕ, s ≠ 2 * n + 1) :
    riemannZeta s + contourIntegral s (1 / 2)
      + Complex.chi s * mirrorContourIntegral (1 - s) (1 / 2) = 0 := by
  rw [riemannZeta_add_contourIntegral_half_eq hs, mirrorContourIntegral_one_sub_eq hs,
    show ((2 * π : ℝ) : ℂ) = 2 * (π : ℂ) by push_cast; ring]
  linear_combination (-(exp (-((π / 4 : ℝ) * I * (2 - s))) * mirrorHankelIntegral (1 - s))) *
    Complex.chi_mul_cos hodd
private theorem isClosed_range_two_mul_natCast_add_one :
    IsClosed (Set.range fun n : ℕ ↦ 2 * (n : ℂ) + 1) := by
  simpa [Set.range_comp, Function.comp_def] using
    (((Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).trans (Homeomorph.addRight 1)).isClosedMap.comp
      (Complex.isometry_ofReal.isClosedEmbedding.isClosedMap.comp
        Nat.isClosedEmbedding_coe_real.isClosedMap)).isClosed_range
theorem riemannZeta_add_contourIntegral_add_chi_mul_mirror_eq_zero {s : ℂ}
    (hodd : ∀ n : ℕ, s ≠ 2 * n + 1) :
    riemannZeta s + contourIntegral s (1 / 2)
      + Complex.chi s * mirrorContourIntegral (1 - s) (1 / 2) = 0 := by
  set S : Set ℂ := Set.range fun n : ℕ ↦ 2 * (n : ℂ) + 1 with hS
  have hmem : ∀ z : ℂ, z ∈ Sᶜ ↔ ∀ n : ℕ, z ≠ 2 * n + 1 := fun z ↦ by simp [hS, eq_comm]
  set F : ℂ → ℂ := fun z ↦ riemannZeta z + contourIntegral z (1 / 2)
    + Complex.chi z * mirrorContourIntegral (1 - z) (1 / 2)
  have hdiff : DifferentiableOn ℂ F Sᶜ := fun z hz ↦ by
    have hz' := (hmem z).1 hz
    exact (((differentiableAt_riemannZeta fun h ↦ hz' 0 (by rw [h]; norm_num)).add
      (differentiable_contourIntegral_of_le_half (by norm_num) le_rfl z)).add
      ((Complex.differentiableAt_chi hz').mul
        (differentiable_mirrorContourIntegral_one_sub (by norm_num) le_rfl z)))
      |>.differentiableWithinAt
  have hconn : IsPreconnected (Sᶜ : Set ℂ) :=
    ((Set.countable_range _).isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have hz₀ : (2 + I : ℂ) ∈ (Sᶜ : Set ℂ) :=
    (hmem _).2 fun n h ↦ by simpa using congrArg Complex.im h
  have hev : F =ᶠ[𝓝 (2 + I : ℂ)] 0 := by
    have hU : IsOpen {z : ℂ | 1 < z.re ∧ z.im ≠ 0} :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_ne.preimage continuous_im)
    filter_upwards [hU.mem_nhds (show 1 < (2 + I : ℂ).re ∧ (2 + I : ℂ).im ≠ 0 by norm_num)]
      with z hz
    exact riemannZeta_add_contourIntegral_add_chi_mul_mirror_eq_zero_of_one_lt hz.1
      fun n h ↦ hz.2 (by simpa using congrArg Complex.im h)
  exact (hdiff.analyticOnNhd isClosed_range_two_mul_natCast_add_one.isOpen_compl)
    |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz₀ hev ((hmem s).2 hodd)
theorem riemannZeta_eq_neg_contourIntegral_sub {t : ℝ} (ht : 0 < t) :
    riemannZeta (1 / 2 + t * I)
      = -contourIntegral (1 / 2 + t * I) (1 / 2)
        - exp (-(2 * (riemannSiegelTheta t : ℂ)) * I) *
          (starRingEnd ℂ) (contourIntegral (1 / 2 + t * I) (1 / 2)) := by
  have hodd : ∀ n : ℕ, (1 / 2 + (t : ℂ) * I) ≠ 2 * n + 1 := fun n h ↦
    ht.ne' (by simpa using congrArg Complex.im h)
  have hmirror : mirrorContourIntegral (1 - (1 / 2 + (t : ℂ) * I)) (1 / 2)
      = starRingEnd ℂ (contourIntegral (1 / 2 + (t : ℂ) * I) (1 / 2)) := by
    rw [mirrorContourIntegral, show (1 : ℂ) - (1 / 2 + (t : ℂ) * I)
      = starRingEnd ℂ (1 / 2 + (t : ℂ) * I) by norm_num [Complex.ext_iff], Complex.conj_conj]
  have hchi : Complex.chi (1 / 2 + (t : ℂ) * I) = exp (-(2 * (riemannSiegelTheta t : ℂ)) * I) := by
    rw [mul_comm (t : ℂ) I]; exact Complex.chi_half_add_mul_I ht.le
  have h := riemannZeta_add_contourIntegral_add_chi_mul_mirror_eq_zero hodd
  rw [hmirror, hchi] at h
  linear_combination h
end Zeta.RiemannSiegel
end
end CertificatePort128


section CertificatePort129
section
open Complex
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def mainSum (t : ℝ) (ν : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 1 ν, Real.cos (riemannSiegelTheta t - t * Real.log n) / Real.sqrt n
theorem mainSum_eq_two_re_exp_mul_contourIntegral_sub (t : ℝ) (ν : ℕ) :
    mainSum t ν
      = 2 * (exp (I * riemannSiegelTheta t) *
          contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)).re
        - 2 * (exp (I * riemannSiegelTheta t) * contourIntegral (1 / 2 + t * I) (1 / 2)).re := by
  have hsum : (exp (I * (riemannSiegelTheta t : ℂ)) *
        ∑ n ∈ Finset.Icc 1 ν, (n : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))).re
      = ∑ n ∈ Finset.Icc 1 ν, Real.cos (riemannSiegelTheta t - t * Real.log n) / Real.sqrt n := by
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    rw [← Complex.ofReal_natCast n]
    exact Complex.re_exp_mul_I_mul_cpow_neg hn0 t (riemannSiegelTheta t)
  rw [mainSum, ← hsum, sum_cpow_neg_eq_contourIntegral_sub_contourIntegral, mul_sub,
    Complex.sub_re]
  ring
theorem hardyZ_eq_mainSum_sub {t : ℝ} (ht : 0 < t) (ν : ℕ) :
    hardyZ t = mainSum t ν
      - 2 * (exp (I * riemannSiegelTheta t) *
          contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)).re := by
  set θ : ℝ := riemannSiegelTheta t with hθ
  set J : ℂ := contourIntegral (1 / 2 + t * I) (1 / 2)
  have hphase : exp (I * (θ : ℂ)) * (exp (-(2 * (θ : ℂ)) * I) * (starRingEnd ℂ) J)
      = (starRingEnd ℂ) (exp (I * (θ : ℂ)) * J) := by
    rw [map_mul, ← Complex.exp_conj, ← mul_assoc, ← exp_add, map_mul, Complex.conj_I,
      Complex.conj_ofReal, show I * (θ : ℂ) + -(2 * (θ : ℂ)) * I = -I * (θ : ℂ) by ring]
  have hkey : hardyZ t = -(2 * (exp (I * (θ : ℂ)) * J).re) := by
    rw [hardyZ, ← hθ, show (1 / 2 + I * (t : ℂ)) = 1 / 2 + (t : ℂ) * I by ring,
      riemannZeta_eq_neg_contourIntegral_sub ht, mul_sub, mul_neg, hphase,
      show -(exp (I * (θ : ℂ)) * J) - (starRingEnd ℂ) (exp (I * (θ : ℂ)) * J)
        = -(exp (I * (θ : ℂ)) * J + (starRingEnd ℂ) (exp (I * (θ : ℂ)) * J)) by ring,
      Complex.add_conj]
    simp
  rw [mainSum_eq_two_re_exp_mul_contourIntegral_sub, hkey]
  ring
theorem mainSum_eq_mainSumOfPhase (t : ℝ) (ν : ℕ) :
    mainSum t ν = mainSumOfPhase (riemannSiegelTheta t) t ν := rfl
theorem abs_mainSumOfPhase_sub_mainSumOfPhase_le (θ₁ θ₂ t : ℝ) (ν : ℕ) :
    |mainSumOfPhase θ₁ t ν - mainSumOfPhase θ₂ t ν| ≤ 4 * Real.sqrt ν * |θ₁ - θ₂| := by
  have hterm : ∀ n ∈ Finset.Icc 1 ν,
      |Real.cos (θ₁ - t * Real.log n) / Real.sqrt n
        - Real.cos (θ₂ - t * Real.log n) / Real.sqrt n| ≤ |θ₁ - θ₂| * (1 / Real.sqrt n) := by
    intro n hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.2 (Finset.mem_Icc.1 hn).1)
    rw [div_sub_div_same, abs_div, abs_of_pos hs, mul_one_div]
    gcongr ?_ / _
    simpa using Real.abs_cos_sub_cos_le (θ₁ - t * Real.log n) (θ₂ - t * Real.log n)
  calc |mainSumOfPhase θ₁ t ν - mainSumOfPhase θ₂ t ν|
      = 2 * |∑ n ∈ Finset.Icc 1 ν, (Real.cos (θ₁ - t * Real.log n) / Real.sqrt n
              - Real.cos (θ₂ - t * Real.log n) / Real.sqrt n)| := by
        rw [mainSumOfPhase, mainSumOfPhase, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_two]
    _ ≤ 2 * ∑ n ∈ Finset.Icc 1 ν, |θ₁ - θ₂| * (1 / Real.sqrt n) := by
        gcongr; exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = 2 * (|θ₁ - θ₂| * ∑ n ∈ Finset.Icc 1 ν, 1 / Real.sqrt n) := by rw [← Finset.mul_sum]
    _ ≤ 2 * (|θ₁ - θ₂| * (2 * Real.sqrt ν)) := by gcongr; exact Real.sum_one_div_sqrt_le ν
    _ = 4 * Real.sqrt ν * |θ₁ - θ₂| := by ring
end Zeta.RiemannSiegel
end
end CertificatePort129


section CertificatePort130
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
private theorem rpow_neg_quarter_div_self {T : ℝ} (hT : 0 < T) :
    T ^ (-(1 / 4) : ℝ) / T = T ^ (-(5 / 4) : ℝ) := by
  rw [div_eq_mul_inv, ← Real.rpow_neg_one T, ← Real.rpow_add hT]
  norm_num
private theorem hardyZ_sub_mainSum_add_two_mul_re_eq {t : ℝ} (ht : 0 < t) (ν : ℕ) (Y : ℂ) :
    hardyZ t - mainSum t ν
        + 2 * (((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
            * (exp (-((π / 8 : ℝ) * I)) * Y)).re
      = -2 * (((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
            * ((exp (I * ((riemannSiegelTheta t - leadingTheta t : ℝ) : ℂ)) - 1)
              * (exp (-((π / 8 : ℝ) * I)) * Y))).re
        - 2 * (exp (I * (riemannSiegelTheta t : ℂ))
            * (contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2) - saddleFactor t ν * Y)).re := by
  have hexp : exp (I * (riemannSiegelTheta t : ℂ)) * exp (-(I * ((leadingTheta t : ℂ) + π / 8)))
      = exp (I * ((riemannSiegelTheta t - leadingTheta t : ℝ) : ℂ)) * exp (-((π / 8 : ℝ) * I)) := by
    rw [← exp_add, ← exp_add]
    exact congrArg _ (by push_cast; ring)
  have hkey : exp (I * (riemannSiegelTheta t : ℂ)) * (saddleFactor t ν * Y)
      = ((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
            * (exp (-((π / 8 : ℝ) * I)) * Y)
        + ((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
            * ((exp (I * ((riemannSiegelTheta t - leadingTheta t : ℝ) : ℂ)) - 1)
              * (exp (-((π / 8 : ℝ) * I)) * Y)) := by
    rw [saddleFactor, show ((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
      = (-1 : ℂ) ^ ν * (((t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ) from by push_cast; ring]
    linear_combination ((-1 : ℂ) ^ ν * (((t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ) * Y) * hexp
  rw [hardyZ_eq_mainSum_sub ht ν,
    show exp (I * (riemannSiegelTheta t : ℂ))
        * contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)
      = exp (I * (riemannSiegelTheta t : ℂ)) * (saddleFactor t ν * Y)
        + exp (I * (riemannSiegelTheta t : ℂ))
            * (contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2) - saddleFactor t ν * Y) by ring,
    hkey]
  simp only [Complex.add_re]
  ring
private theorem norm_ofReal_neg_one_pow_mul_rpow {t : ℝ} (ht : 0 < t / (2 * π)) (ν : ℕ) :
    ‖((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)‖
      = (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by
  simp [abs_of_pos (Real.rpow_pos_of_pos ht _)]
private theorem abs_two_mul_re_phase_swap_le {t : ℝ} (hT0 : 0 < t / (2 * π)) (ν : ℕ) {Y : ℂ}
    {φ B : ℝ} (hY : ‖Y‖ ≤ B)
    (hphase : ‖exp (I * ((riemannSiegelTheta t - leadingTheta t : ℝ) : ℂ)) - 1‖ ≤ φ) :
    |2 * (((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
        * ((exp (I * ((riemannSiegelTheta t - leadingTheta t : ℝ) : ℂ)) - 1)
          * (exp (-((π / 8 : ℝ) * I)) * Y))).re|
      ≤ 2 * ((t / (2 * π)) ^ (-(1 / 4) : ℝ) * (φ * B)) := by
  have hEY : ‖exp (-((π / 8 : ℝ) * I)) * Y‖ ≤ B := by simpa [Complex.norm_exp] using hY
  rw [abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by norm_num)
  rw [norm_mul, norm_mul, norm_ofReal_neg_one_pow_mul_rpow hT0 ν]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hphase hEY (norm_nonneg _)
    ((norm_nonneg _).trans hphase)) (Real.rpow_nonneg hT0.le _)
private theorem abs_two_mul_re_exp_I_mul_le {t R : ℝ} {Z : ℂ} (h : ‖Z‖ ≤ R) :
    |2 * (exp (I * (riemannSiegelTheta t : ℂ)) * Z).re| ≤ 2 * R := by
  rw [abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by norm_num)
  simpa [Complex.norm_exp] using h
private theorem abs_hardyZ_sub_mainSum_add_two_mul_re_le {t : ℝ} (hT0 : 0 < t / (2 * π)) (ν : ℕ)
    {Y : ℂ} {φ B R : ℝ} (hY : ‖Y‖ ≤ B)
    (hphase : ‖exp (I * ((riemannSiegelTheta t - leadingTheta t : ℝ) : ℂ)) - 1‖ ≤ φ)
    (hsaddle : ‖contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2) - saddleFactor t ν * Y‖ ≤ R) :
    |hardyZ t - mainSum t ν
        + 2 * (((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
            * (exp (-((π / 8 : ℝ) * I)) * Y)).re|
      ≤ 2 * ((t / (2 * π)) ^ (-(1 / 4) : ℝ) * (φ * B)) + 2 * R := by
  have hb1 := abs_two_mul_re_phase_swap_le hT0 ν hY hphase
  have hb2 := abs_two_mul_re_exp_I_mul_le (t := t) hsaddle
  rw [hardyZ_sub_mainSum_add_two_mul_re_eq
    ((div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)).mp hT0) ν, abs_le]
  rw [abs_le] at hb1 hb2
  constructor <;> linarith
theorem norm_contourIntegral_sub_modelIntegral_sub_moment_le {t : ℝ} (ht : 16 ≤ t / (2 * π))
    {ν : ℕ} (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) :
    ‖contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)
        - saddleFactor t ν * (modelIntegral ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2)
            - iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2))
                  ((Real.sqrt (t / (2 * π)) - ν : ℝ)) / (96 * (π : ℂ) ^ 2)
                / ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ))‖
      ≤ 61 / 20 * (t / (2 * π)) ^ (-(5 / 4) : ℝ) := by
  have hT0 : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  have ht0 : 0 < t := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)).mp hT0
  have hinner := norm_integral_inner_sub_linear_le ht hν hν'
  have hlin := norm_integral_linear_add_iteratedDeriv_three_modelIntegral_le ht hν hν'
  have houter := norm_integral_outer_le' ht hν hν'
  have hfac := contourIntegral_sub_mul_modelIntegral ht0 ν
  have hFint := integrable_modelIntegrand_mul_exp_saddleDiscrepancy_sub_one ht0 ν
  have hLint := integrable_modelIntegrand_mul_saddleLinear_div
    ((Real.sqrt (t / (2 * π)) - ν : ℝ) : ℂ) ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ)
  set S : ℝ := Real.sqrt (t / (2 * π))
  set p : ℝ := S - (ν : ℝ)
  set W : ℝ := sharpSplitRadius t
  set D : ℂ := iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ) / (96 * (π : ℂ) ^ 2)
    / (S : ℂ)
  rw [funext fun w : ℝ ↦ mul_sub (modelIntegrand (p : ℂ) (1 / 2) w)
      (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)
      (saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ)),
    integral_sub hFint.integrableOn hLint.integrableOn] at hinner
  have hkey : (1 + I) * (∫ w : ℝ, modelIntegrand (p : ℂ) (1 / 2) w
        * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)) + D
      = (1 + I) * ((∫ w in Set.Icc (-W) W, modelIntegrand (p : ℂ) (1 / 2) w
              * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1))
            - ∫ w in Set.Icc (-W) W, modelIntegrand (p : ℂ) (1 / 2) w
                * (saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ)))
        + ((1 + I) * (∫ w in Set.Icc (-W) W, modelIntegrand (p : ℂ) (1 / 2) w
              * (saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))) + D)
        + (1 + I) * ∫ w in (Set.Icc (-W) W)ᶜ, modelIntegrand (p : ℂ) (1 / 2) w
              * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1) := by
    rw [← integral_add_compl measurableSet_Icc hFint]
    ring
  have hbound : ‖(1 + I) * (∫ w : ℝ, modelIntegrand (p : ℂ) (1 / 2) w
        * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)) + D‖
      ≤ 61 / 20 / (t / (2 * π)) := by
    rw [hkey]
    refine norm_add₃_le.trans ((add_le_add (add_le_add hinner hlin) houter).trans ?_)
    rw [← add_div, ← add_div, div_le_div_iff_of_pos_right hT0]
    norm_num
  rw [show contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)
        - saddleFactor t ν * (modelIntegral (p : ℂ) (1 / 2) - D)
      = saddleFactor t ν * ((1 + I) * (∫ w : ℝ, modelIntegrand (p : ℂ) (1 / 2) w
          * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)) + D) by
      linear_combination hfac,
    norm_mul, norm_saddleFactor ht0 ν]
  refine (mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hT0.le _)).trans_eq ?_
  rw [← rpow_neg_quarter_div_self hT0]
  ring
private theorem two_mul_re_exp_mul_modelIntegral_sub_moment_eq (p : ℝ) {S : ℝ} (hS : 0 < S) :
    2 * (exp (-((π / 8 : ℝ) * I))
        * (modelIntegral (p : ℂ) (1 / 2)
            - iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ) / (96 * (π : ℂ) ^ 2)
              / (S : ℂ))).re
      = correction p + correctionLinear p / S := by
  have hSC : ((S : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hS.ne'
  have hsplit : exp (-((π / 8 : ℝ) * I))
      * (modelIntegral (p : ℂ) (1 / 2)
          - iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ) / (96 * (π : ℂ) ^ 2)
            / (S : ℂ))
      = exp (-((π / 8 : ℝ) * I)) * modelIntegral (p : ℂ) (1 / 2)
        + ((-(1 / (96 * π ^ 2 * S)) : ℝ) : ℂ)
            * (exp (-((π / 8 : ℝ) * I))
                * iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)) := by
    push_cast
    field_simp
    ring
  rw [correctionLinear_eq, iteratedDeriv_three_correction p, hsplit, Complex.add_re,
    Complex.re_ofReal_mul, correction]
  field_simp
theorem abs_hardyZ_sub_mainSum_sub_correction_sub_correctionLinear_le {t : ℝ}
    (ht : 16 ≤ t / (2 * π)) {ν : ℕ}
    (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) :
    |hardyZ t - mainSum t ν
        + (-1) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ)
            * (correction (Real.sqrt (t / (2 * π)) - ν)
              + correctionLinear (Real.sqrt (t / (2 * π)) - ν) / Real.sqrt (t / (2 * π)))|
      ≤ 25 / 4 * (t / (2 * π)) ^ (-(5 / 4) : ℝ) := by
  have hpi := Real.pi_gt_three
  have hT0 : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  have ht0 : 0 < t := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)).mp hT0
  have ht32 : 32 * π ≤ t := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * π)] at ht
    linarith
  have hS0 : (0 : ℝ) < Real.sqrt (t / (2 * π)) := Real.sqrt_pos.2 hT0
  have hS4 : (4 : ℝ) ≤ Real.sqrt (t / (2 * π)) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hp0 : 0 ≤ Real.sqrt (t / (2 * π)) - (ν : ℝ) := by linarith
  have hp1 : Real.sqrt (t / (2 * π)) - (ν : ℝ) ≤ 1 := by linarith
  have hR0 : (0 : ℝ) ≤ (t / (2 * π)) ^ (-(5 / 4) : ℝ) := Real.rpow_nonneg hT0.le _
  have hphase : ‖exp (I * ((riemannSiegelTheta t - leadingTheta t : ℝ) : ℂ)) - 1‖
      ≤ 101 / (4800 * t) :=
    (Real.norm_exp_I_mul_ofReal_sub_one_le.trans_eq (Real.norm_eq_abs _)).trans
      (abs_riemannSiegelTheta_sub_leading_le' ht32)
  have hsaddle := norm_contourIntegral_sub_modelIntegral_sub_moment_le ht hν hν'
  set S : ℝ := Real.sqrt (t / (2 * π))
  set p : ℝ := S - (ν : ℝ)
  set Y : ℂ := modelIntegral (p : ℂ) (1 / 2)
    - iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ) / (96 * (π : ℂ) ^ 2)
      / (S : ℂ)
  have hY : ‖Y‖ ≤ 13 / 10 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS0, norm_mul,
      norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      div_div]
    have hstep : ‖iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)‖
        / (96 * π ^ 2 * S) ≤ 1 / 5 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 5)]
      nlinarith [norm_iteratedDeriv_three_modelIntegral_le' hp0 hp1,
        mul_le_mul_of_nonneg_right (by nlinarith : (9 : ℝ) ≤ π ^ 2) hS0.le, hS4]
    linarith [norm_modelIntegral_le' hp0 hp1]
  have hre : 2 * (((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
        * (exp (-((π / 8 : ℝ) * I)) * Y)).re
      = (-1) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) * (correction p + correctionLinear p / S) := by
    rw [Complex.re_ofReal_mul]
    linear_combination ((-1 : ℝ) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ))
      * two_mul_re_exp_mul_modelIntegral_sub_moment_eq p hS0
  rw [← hre]
  refine (abs_hardyZ_sub_mainSum_add_two_mul_re_le hT0 ν hY hphase hsaddle).trans ?_
  rw [show 2 * ((t / (2 * π)) ^ (-(1 / 4) : ℝ) * (101 / (4800 * t) * (13 / 10)))
      = 1313 / (24000 * (2 * π)) * (t / (2 * π)) ^ (-(5 / 4) : ℝ) from by
    rw [← rpow_neg_quarter_div_self hT0]
    field_simp
    ring]
  have hcoef : (1313 : ℝ) / (24000 * (2 * π)) ≤ 1 / 50 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hcoef hR0]
theorem abs_hardyZ_sub_mainSumOfPhase_sub_correction_sub_correctionLinear_le {t : ℝ}
    (ht : 16 ≤ t / (2 * π)) {θ' ε : ℝ} (hθ : |riemannSiegelTheta t - θ'| ≤ ε) :
    |hardyZ t - mainSumOfPhase θ' t ⌊Real.sqrt (t / (2 * π))⌋₊
        + (-1) ^ (⌊Real.sqrt (t / (2 * π))⌋₊ : ℕ) * (t / (2 * π)) ^ (-(1 / 4) : ℝ)
            * (correction (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
              + correctionLinear (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
                  / Real.sqrt (t / (2 * π)))|
      ≤ 25 / 4 * (t / (2 * π)) ^ (-(5 / 4) : ℝ)
        + 4 * Real.sqrt ⌊Real.sqrt (t / (2 * π))⌋₊ * ε := by
  have hsharp := abs_hardyZ_sub_mainSum_sub_correction_sub_correctionLinear_le ht
    (Nat.floor_le (Real.sqrt_nonneg (t / (2 * π)))) (Nat.lt_floor_add_one _).le
  have hlip : |mainSum t ⌊Real.sqrt (t / (2 * π))⌋₊
      - mainSumOfPhase θ' t ⌊Real.sqrt (t / (2 * π))⌋₊|
      ≤ 4 * Real.sqrt ⌊Real.sqrt (t / (2 * π))⌋₊ * ε := by
    rw [mainSum_eq_mainSumOfPhase]
    exact (abs_mainSumOfPhase_sub_mainSumOfPhase_le _ _ t _).trans
      (mul_le_mul_of_nonneg_left hθ (by positivity))
  rw [abs_le] at hsharp hlip ⊢
  constructor <;> linarith
theorem abs_hardyZ_sub_mainSumOfPhase_sub_correction_sub_correctionLinear_le' {t : ℝ}
    (ht : 16 ≤ t / (2 * π)) :
    |hardyZ t
        - mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ⌊Real.sqrt (t / (2 * π))⌋₊
        + (-1) ^ (⌊Real.sqrt (t / (2 * π))⌋₊ : ℕ) * (t / (2 * π)) ^ (-(1 / 4) : ℝ)
            * (correction (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
              + correctionLinear (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
                  / Real.sqrt (t / (2 * π)))|
      ≤ 25 / 4 * (t / (2 * π)) ^ (-(5 / 4) : ℝ)
        + 1 / 32 * (t / (2 * π)) ^ (-(15 / 4) : ℝ) := by
  have hT0 : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  have ht0 : 0 < t := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)).mp hT0
  refine (abs_hardyZ_sub_mainSumOfPhase_sub_correction_sub_correctionLinear_le ht
    (abs_riemannSiegelTheta_sub_approximant_two_le ht0)).trans ?_
  have hq : Real.sqrt ⌊Real.sqrt (t / (2 * π))⌋₊ ≤ (t / (2 * π)) ^ (1 / 4 : ℝ) := by
    refine (Real.sqrt_le_sqrt (Nat.floor_le (Real.sqrt_nonneg _))).trans ?_
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le]
    norm_num
  have hpow : (t / (2 * π)) ^ (1 / 4 : ℝ) / (t / (2 * π)) ^ (4 : ℕ)
      = (t / (2 * π)) ^ (-(15 / 4) : ℝ) := by
    rw [← Real.rpow_natCast (t / (2 * π)) 4, ← Real.rpow_sub hT0]
    norm_num
  have ht4 : t ^ 4 = (2 * π) ^ 4 * (t / (2 * π)) ^ 4 := by
    rw [div_pow, mul_div_cancel₀ _ (by positivity : ((2 : ℝ) * π) ^ 4 ≠ 0)]
  have hcoef : (48 : ℝ) / (2 * π) ^ 4 ≤ 1 / 32 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6.28)
      (by linarith [Real.pi_gt_d2] : (6.28 : ℝ) ≤ 2 * π) 4]
  refine add_le_add le_rfl ?_
  calc 4 * Real.sqrt ⌊Real.sqrt (t / (2 * π))⌋₊ * (12 / t ^ 4)
      ≤ 4 * (t / (2 * π)) ^ (1 / 4 : ℝ) * (12 / t ^ 4) := by gcongr
    _ = 48 / (2 * π) ^ 4 * ((t / (2 * π)) ^ (1 / 4 : ℝ) / (t / (2 * π)) ^ (4 : ℕ)) := by
        rw [ht4]
        field_simp
        ring
    _ = 48 / (2 * π) ^ 4 * (t / (2 * π)) ^ (-(15 / 4) : ℝ) := by rw [hpow]
    _ ≤ 1 / 32 * (t / (2 * π)) ^ (-(15 / 4) : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hT0.le _)
end Zeta.RiemannSiegel
open Zeta.RiemannSiegel
theorem abs_hardyZRemainderRS_le {t : ℝ} (ht : 16 ≤ t / (2 * π)) :
    |hardyZRemainderRS t| ≤ hardyZErrorBoundRS t := by
  refine (le_of_eq (congrArg abs ?_)).trans
    (abs_hardyZ_sub_mainSumOfPhase_sub_correction_sub_correctionLinear_le' ht)
  ring
theorem abs_hardyZRemainderRS₀_le {t : ℝ} (ht : 16 ≤ t / (2 * π)) :
    |hardyZRemainderRS₀ t| ≤ hardyZErrorBoundRS₀ t := by
  have hT : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  set T := t / (2 * π) with hTdef
  set ν := ⌊Real.sqrt T⌋₊ with hνdef
  set p := Real.sqrt T - (ν : ℝ) with hpdef
  have hp0 : 0 ≤ p := sub_nonneg.2 (Nat.floor_le (Real.sqrt_nonneg T))
  have hp1 : p ≤ 1 := by
    have := Nat.lt_floor_add_one (Real.sqrt T)
    rw [hpdef]; linarith
  have hsplit : hardyZRemainderRS₀ t
      = hardyZRemainderRS t
        - (-1) ^ ν * T ^ (-(1 / 4) : ℝ) * (correctionLinear p / Real.sqrt T) := by
    simp only [hardyZRemainderRS₀, hardyZRemainderRS, hardyZApproximantRS₀, hardyZApproximantRS,
      ← hTdef, ← hνdef, ← hpdef]
    ring
  have hsqrtT : Real.sqrt T = T ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow T
  have hdrop : |(-1 : ℝ) ^ ν * T ^ (-(1 / 4) : ℝ) * (correctionLinear p / Real.sqrt T)|
      ≤ 13 / 10 * T ^ (-(3 / 4) : ℝ) := by
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_div,
      abs_of_pos (Real.rpow_pos_of_pos hT _), abs_of_pos (Real.sqrt_pos.2 hT), hsqrtT]
    have hpos : (0 : ℝ) < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hT _
    calc T ^ (-(1 / 4) : ℝ) * (|correctionLinear p| / T ^ (1 / 2 : ℝ))
        ≤ T ^ (-(1 / 4) : ℝ) * (13 / 10 / T ^ (1 / 2 : ℝ)) := by
          gcongr
          exact abs_correctionLinear_le hp0 hp1
      _ = 13 / 10 * (T ^ (-(1 / 4) : ℝ) / T ^ (1 / 2 : ℝ)) := by ring
      _ = 13 / 10 * T ^ (-(3 / 4) : ℝ) := by rw [← Real.rpow_sub hT]; norm_num
  calc |hardyZRemainderRS₀ t|
      = |hardyZRemainderRS t
          + -((-1 : ℝ) ^ ν * T ^ (-(1 / 4) : ℝ) * (correctionLinear p / Real.sqrt T))| := by
        rw [hsplit, sub_eq_add_neg]
    _ ≤ |hardyZRemainderRS t|
          + |(-1 : ℝ) ^ ν * T ^ (-(1 / 4) : ℝ) * (correctionLinear p / Real.sqrt T)| := by
        rw [← abs_neg ((-1 : ℝ) ^ ν * T ^ (-(1 / 4) : ℝ) * (correctionLinear p / Real.sqrt T))]
        exact abs_add_le _ _
    _ ≤ hardyZErrorBoundRS t + 13 / 10 * T ^ (-(3 / 4) : ℝ) :=
        add_le_add (abs_hardyZRemainderRS_le ht) hdrop
end
end CertificatePort130


section CertificatePort131
section
open Zeta.Certificates
theorem riemannZeta.exists_zero_of_approx_sign_change {a b va vb : ℝ} (hab : a ≤ b)
    (ha : 0 ≤ a) (hsign : va * vb < 0) (hL : |hardyZ a - va| < |va|)
    (hR : |hardyZ b - vb| < |vb|) :
    ∃ t ∈ Set.Ioo a b, riemannZeta (1 / 2 + Complex.I * t) = 0 := by
  have hsL : 0 < hardyZ a * va := mul_pos_of_abs_sub_lt hL
  have hsR : 0 < hardyZ b * vb := mul_pos_of_abs_sub_lt hR
  have hprod : hardyZ a * hardyZ b < 0 := by
    nlinarith [mul_pos hsL hsR, hsign]
  have hcont : ContinuousOn hardyZ (Set.Icc a b) :=
    continuousOn_hardyZ.mono fun x hx ↦ ha.trans hx.1
  obtain ⟨t₀, ht₀mem, ht₀⟩ : ∃ t₀ ∈ Set.Icc a b, hardyZ t₀ = 0 := by
    rcases mul_neg_iff.mp hprod with ⟨hlp, hrn⟩ | ⟨hln, hrp⟩
    · exact intermediate_value_Icc' hab hcont ⟨hrn.le, hlp.le⟩
    · exact intermediate_value_Icc hab hcont ⟨hln.le, hrp.le⟩
  have hlne : hardyZ a ≠ 0 := left_ne_zero_of_mul hsL.ne'
  have hrne : hardyZ b ≠ 0 := left_ne_zero_of_mul hsR.ne'
  have ht₀Ioo : t₀ ∈ Set.Ioo a b :=
    ⟨lt_of_le_of_ne ht₀mem.1 fun heq ↦ hlne (by rw [heq]; exact ht₀),
     lt_of_le_of_ne ht₀mem.2 fun heq ↦ hrne (by rw [← heq]; exact ht₀)⟩
  exact ⟨t₀, ht₀Ioo, (hardyZ_eq_zero_iff_riemannZeta (ha.trans ht₀Ioo.1.le)).mp ht₀⟩
theorem riemannZeta.exists_zero_of_zIntervalRS_certificate (I : ZIntervalRS) (h : I.Certificate) :
    ∃ t ∈ Set.Ioo I.fst I.snd, riemannZeta (1 / 2 + Complex.I * t) = 0 :=
  riemannZeta.exists_zero_of_approx_sign_change I.fst_le_snd h.fst_nonneg h.is_sign_change
    ((abs_hardyZRemainderRS_le h.sixteen_le_fst_div).trans_lt
      (by simpa [Real.norm_eq_abs] using h.fst_error))
    ((abs_hardyZRemainderRS_le h.sixteen_le_snd_div).trans_lt
      (by simpa [Real.norm_eq_abs] using h.snd_error))
theorem riemannZeta.exists_zero_of_zIntervalRS_certificate₀ (I : ZIntervalRS)
    (h : I.Certificate₀) :
    ∃ t ∈ Set.Ioo I.fst I.snd, riemannZeta (1 / 2 + Complex.I * t) = 0 := by
  have h16 {t : ℝ} (ht : 32 * Real.pi ≤ t) : 16 ≤ t / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  exact riemannZeta.exists_zero_of_approx_sign_change I.fst_le_snd h.fst_nonneg h.is_sign_change
    ((abs_hardyZRemainderRS₀_le (h16 h.le_fst)).trans_lt
      (by simpa [Real.norm_eq_abs] using h.fst_error))
    ((abs_hardyZRemainderRS₀_le (h16 h.le_snd)).trans_lt
      (by simpa [Real.norm_eq_abs] using h.snd_error))
theorem riemannZeta.exists_zero_of_zIntervalRS_certified (I : ZIntervalRS) (h : I.Certified) :
    ∃ t ∈ Set.Ioo I.fst I.snd, riemannZeta (1 / 2 + Complex.I * t) = 0 :=
  h.elim (riemannZeta.exists_zero_of_zIntervalRS_certificate I)
    (riemannZeta.exists_zero_of_zIntervalRS_certificate₀ I)
end
end CertificatePort131


section CertificatePort132
section
namespace Enclosure
noncomputable def sfrac (neg : Bool) (cn cd : ℕ) : ℝ := (if neg then -1 else 1) * ((cn : ℝ) / cd)
theorem sfrac_not (neg : Bool) (cn cd : ℕ) : sfrac (!neg) cn cd = - sfrac neg cn cd := by
  cases neg <;> simp [sfrac]
theorem sfrac_false_div (cn cd : ℕ) : sfrac false cn cd = (cn : ℝ) / cd := by simp [sfrac]
theorem sfrac_true_div (cn cd : ℕ) : sfrac true cn cd = (-(cn : ℝ)) / cd := by simp [sfrac, neg_div]
theorem ofScientific_dyadic_arg (m e v : ℕ) (hv : (Nat.pow 10 e).beq v = true) :
    (OfScientific.ofScientific m true e : ℝ) = (m : ℝ) / (v : ℝ) := by
  have hv : 10 ^ e = v := Nat.eq_of_beq_eq_true hv
  subst hv
  rw [← Rat.cast_ofScientific, Rat.ofScientific_def_eq_if]
  simp
theorem sfrac_natCast (n : ℕ) : (n : ℝ) = sfrac false n 1 := by simp [sfrac]
theorem sfrac_zero_eq : (0 : ℝ) = sfrac false (nat_lit 0) (nat_lit 1) := by simp [sfrac]
theorem sfrac_one_eq : (1 : ℝ) = sfrac false (nat_lit 1) (nat_lit 1) := by simp [sfrac]
theorem sfrac_neg_eq (x : ℝ) (neg : Bool) (num den : ℕ) (h : x = sfrac neg num den) :
    -x = sfrac (!neg) num den := by rw [h, sfrac_not]
theorem sfrac_div_eq (na nb : ℝ) (an bn : ℕ) (aneg bneg : Bool)
    (hn : na = sfrac aneg an 1) (hd : nb = sfrac bneg bn 1) :
    na / nb = sfrac (aneg != bneg) an bn := by
  rw [hn, hd]
  cases aneg <;> cases bneg <;> simp [sfrac] <;> ring
theorem sfrac_ofScientific_eq (m e v : ℕ) (hv : (Nat.pow 10 e).beq v = true) :
    (OfScientific.ofScientific m true e : ℝ) = sfrac false m v := by
  rw [ofScientific_dyadic_arg m e v hv]; simp [sfrac]
theorem pos_of_ble {n : ℕ} (h : Nat.ble 1 n = true) : 0 < n :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_ble_eq_true h)
theorem pos_real_of_ble {n : ℕ} (h : Nat.ble 1 n = true) : (0 : ℝ) < n := by
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_ble_eq_true h)
theorem dec_le_dec {a b : ℝ} (an av bn bv : ℕ)
    (ha : a = sfrac false an av) (hb : b = sfrac false bn bv)
    (hav : Nat.ble 1 av = true) (hbv : Nat.ble 1 bv = true)
    (h : Nat.ble (an.mul bv) (bn.mul av) = true) : a ≤ b := by
  subst ha hb
  simp only [Nat.ble_eq, Nat.mul_eq] at h
  rw [sfrac_false_div, sfrac_false_div,
    div_le_div_iff₀ (pos_real_of_ble hav) (pos_real_of_ble hbv)]
  exact_mod_cast h
theorem dec_nonneg {a : ℝ} (an av : ℕ) (ha : a = sfrac false an av) : 0 ≤ a := by
  subst ha
  rw [sfrac_false_div]
  exact div_nonneg (Nat.cast_nonneg an) (Nat.cast_nonneg av)
theorem sfrac_ratCast_natDiv (p Q : ℕ) : (((p : ℚ) / (Q : ℚ) : ℚ) : ℝ) = sfrac false p Q := by
  rw [sfrac_false_div]; push_cast; ring
theorem sfrac_ratCast_intSub_nonneg (mp mn Q : ℕ) (hge : Nat.ble mn mp = true) :
    (((((mp : ℤ) - (mn : ℤ) : ℤ) : ℚ) / (Q : ℚ) : ℚ) : ℝ) = sfrac false (mp - mn) Q := by
  simp only [Nat.ble_eq] at hge
  rw [sfrac_false_div]; push_cast [Nat.cast_sub hge]; ring
theorem sfrac_ratCast_intSub_neg (mp mn Q : ℕ) (hle : Nat.ble mp mn = true) :
    (((((mp : ℤ) - (mn : ℤ) : ℤ) : ℚ) / (Q : ℚ) : ℚ) : ℝ) = sfrac true (mn - mp) Q := by
  simp only [Nat.ble_eq] at hle
  rw [sfrac_true_div]; push_cast [Nat.cast_sub hle]; ring
theorem sfrac_ratCast_neg (q : ℚ) (neg : Bool) (num den : ℕ)
    (h : ((q : ℚ) : ℝ) = sfrac neg num den) : ((-q : ℚ) : ℝ) = sfrac (!neg) num den := by
  rw [sfrac_not, ← h]; push_cast; ring
theorem sfrac_pow_eq (x : ℝ) (neg neg' : Bool) (u v n un vn : ℕ)
    (hx : x = sfrac neg u v)
    (hs : (Bool.xor neg' (Bool.and neg ((Nat.mod n 2).beq 1))).not = true)
    (hun : un.beq (Nat.pow u n) = true) (hvn : vn.beq (Nat.pow v n) = true) :
    x ^ n = sfrac neg' un vn := by
  obtain rfl : un = u ^ n := Nat.eq_of_beq_eq_true hun
  obtain rfl : vn = v ^ n := Nat.eq_of_beq_eq_true hvn
  subst hx
  have hdiv : ((u : ℝ) / v) ^ n = ((u ^ n : ℕ) : ℝ) / ((v ^ n : ℕ) : ℝ) := by
    push_cast
    rw [div_pow]
  cases neg with
  | false =>
    obtain rfl : neg' = false := by simpa using hs
    rw [sfrac_false_div, sfrac_false_div, hdiv]
  | true =>
    cases neg' with
    | true =>
      have hodd : Odd n := by
        have h1 : Nat.mod n 2 = 1 := Nat.eq_of_beq_eq_true (by simpa using hs)
        exact Nat.odd_iff.2 (by omega)
      rw [sfrac_true_div, sfrac_true_div, neg_div, neg_div, hodd.neg_pow, hdiv]
    | false =>
      have heven : Even n := by
        have h1 : Nat.beq (Nat.mod n 2) 1 = false := by simpa using hs
        have h2 : n % 2 ≠ 1 := Nat.ne_of_beq_eq_false h1
        exact Nat.even_iff.2 (by omega)
      rw [sfrac_true_div, sfrac_false_div, neg_div, heven.neg_pow, hdiv]
end Enclosure
end
end CertificatePort132


section CertificatePort133
section
namespace Zeta.Certificates
def Separated (C D : CertifiedZeroIntervals) : Prop :=
  ∀ I ∈ C.intervals.getLast?, ∀ J ∈ D.intervals.head?, I.snd ≤ J.fst
theorem separated_of_endpoints {C D : CertifiedZeroIntervals} {b a : ℝ}
    (hC : C.intervals.getLast?.map (·.snd) = some b)
    (hD : D.intervals.head?.map (·.fst) = some a) (h : b ≤ a) : Separated C D := by
  intro I hI J hJ
  rw [Option.mem_def] at hI hJ
  rw [hI, Option.map_some] at hC
  rw [hJ, Option.map_some] at hD
  rw [Option.some.inj hC, Option.some.inj hD]; exact h
theorem CertifiedZeroIntervals.height_le_of_getLast?_snd (C : CertifiedZeroIntervals) {b q : ℝ}
    (h : C.intervals.getLast?.map (·.snd) = some b) (hq : b ≤ q) : C.height ≤ q := by
  obtain ⟨I, hI, hIb⟩ := Option.map_eq_some_iff.mp h
  exact C.height_le_of_getLast? hI (hIb ▸ hq)
abbrev BatchSpec (n an ad bn bd : ℕ) : Prop :=
  ∃ C : CertifiedZeroIntervals, C.intervals.length = n ∧
    C.intervals.head?.map (·.fst) = some (Enclosure.sfrac false an ad) ∧
    C.intervals.getLast?.map (·.snd) = some (Enclosure.sfrac false bn bd)
namespace BatchSpec
variable {n an ad bn bd : ℕ}
noncomputable def bundle (h : BatchSpec n an ad bn bd) : CertifiedZeroIntervals := h.choose
@[simp] theorem bundle_length (h : BatchSpec n an ad bn bd) : h.bundle.intervals.length = n :=
  h.choose_spec.1
@[simp] theorem bundle_head? (h : BatchSpec n an ad bn bd) :
    h.bundle.intervals.head?.map (·.fst) = some (Enclosure.sfrac false an ad) :=
  h.choose_spec.2.1
@[simp] theorem bundle_getLast? (h : BatchSpec n an ad bn bd) :
    h.bundle.intervals.getLast?.map (·.snd) = some (Enclosure.sfrac false bn bd) :=
  h.choose_spec.2.2
end BatchSpec
def CertifiedZeroIntervals.append (C D : CertifiedZeroIntervals) (seam : Separated C D) :
    CertifiedZeroIntervals where
  intervals := C.intervals ++ D.intervals
  fst_nonneg := fun I hI ↦ (List.mem_append.1 hI).elim (C.fst_nonneg I) (D.fst_nonneg I)
  has_zero := fun I hI ↦ (List.mem_append.1 hI).elim (C.has_zero I) (D.has_zero I)
  disj := C.disj.append D.disj seam
@[simp] theorem CertifiedZeroIntervals.append_intervals (C D : CertifiedZeroIntervals)
    (seam : Separated C D) :
    (C.append D seam).intervals = C.intervals ++ D.intervals := rfl
def CertifiedZeroIntervals.ofCertifiedEM
    (l : List (Σ' I : ZIntervalEM, I.Certificate))
    (hdisj : (l.map (fun x ↦ x.1.toNonemptyInterval)).IsChain (fun I J ↦ I.snd ≤ J.fst)) :
    CertifiedZeroIntervals where
  intervals := l.map (fun x ↦ x.1.toNonemptyInterval)
  fst_nonneg := fun _ hI ↦ by
    obtain ⟨⟨_, c⟩, _, rfl⟩ := List.mem_map.1 hI; exact c.fst_nonneg
  has_zero := fun _ hI ↦ by
    obtain ⟨⟨I, c⟩, _, rfl⟩ := List.mem_map.1 hI
    exact riemannZeta.exists_zero_of_zIntervalEM_certificate I c
  disj := hdisj
def CertifiedZeroIntervals.ofCertifiedRS
    (l : List (Σ' I : ZIntervalRS, I.Certified))
    (hdisj : (l.map PSigma.fst).IsChain (fun I J ↦ I.snd ≤ J.fst)) :
    CertifiedZeroIntervals where
  intervals := l.map PSigma.fst
  fst_nonneg := fun _ hI ↦ by
    obtain ⟨⟨_, c⟩, _, rfl⟩ := List.mem_map.1 hI
    exact c.elim (·.fst_nonneg) (·.fst_nonneg)
  has_zero := fun _ hI ↦ by
    obtain ⟨⟨I, c⟩, _, rfl⟩ := List.mem_map.1 hI
    exact riemannZeta.exists_zero_of_zIntervalRS_certified I c
  disj := hdisj
@[simp] theorem CertifiedZeroIntervals.append_getLast?
    (C D : CertifiedZeroIntervals) (seam : Separated C D) (hD : D.intervals ≠ []) :
    (C.append D seam).intervals.getLast? = D.intervals.getLast? :=
  List.getLast?_append_of_ne_nil _ hD
theorem Separated.append_right {A C D : CertifiedZeroIntervals} {seam : Separated A C}
    (hne : C.intervals ≠ []) (h : Separated C D) : Separated (A.append C seam) D := by
  intro I hI J hJ
  rw [CertifiedZeroIntervals.append_getLast? _ _ _ hne] at hI
  exact h I hI J hJ
def CertifiedZeroIntervals.empty : CertifiedZeroIntervals where
  intervals := []
  fst_nonneg := by simp
  has_zero := by simp
  disj := .nil
def CertifiedZeroIntervals.joinAux (acc : CertifiedZeroIntervals) :
    (l : List CertifiedZeroIntervals) → (∀ C ∈ l, C.intervals ≠ []) →
      (∀ C ∈ l.head?, Separated acc C) → l.IsChain Separated → CertifiedZeroIntervals
  | [], _, _, _ => acc
  | C :: r, hne, hacc, h =>
      (acc.append C (hacc C rfl)).joinAux r
        (fun D hD ↦ hne D (List.mem_cons_of_mem _ hD))
        (fun D hD ↦ Separated.append_right (hne C (by simp)) (h.rel_head? hD))
        (List.isChain_cons.mp h).2
def CertifiedZeroIntervals.join : (l : List CertifiedZeroIntervals) →
    (∀ C ∈ l, C.intervals ≠ []) → l.IsChain Separated → CertifiedZeroIntervals
  | [], _, _ => empty
  | C :: r, hne, h =>
      C.joinAux r (fun D hD ↦ hne D (List.mem_cons_of_mem _ hD))
        (fun _ hD ↦ h.rel_head? hD) (List.isChain_cons.mp h).2
theorem CertifiedZeroIntervals.joinAux_intervals (acc : CertifiedZeroIntervals)
    (l : List CertifiedZeroIntervals) (hne : ∀ C ∈ l, C.intervals ≠ [])
    (hacc : ∀ C ∈ l.head?, Separated acc C) (h : l.IsChain Separated) :
    (acc.joinAux l hne hacc h).intervals = acc.intervals ++ (l.map (·.intervals)).flatten := by
  induction l generalizing acc with
  | nil => simp [joinAux]
  | cons C r ih => rw [joinAux, ih]; simp
theorem CertifiedZeroIntervals.joinAux_getLast? (acc : CertifiedZeroIntervals)
    (l : List CertifiedZeroIntervals) (hne : ∀ C ∈ l, C.intervals ≠ [])
    (hacc : ∀ C ∈ l.head?, Separated acc C) (h : l.IsChain Separated) :
    (acc.joinAux l hne hacc h).intervals.getLast? =
      l.getLast?.elim acc.intervals.getLast? (·.intervals.getLast?) := by
  induction l generalizing acc with
  | nil => simp [joinAux]
  | cons C r ih =>
    rw [joinAux, ih]
    have hC : (acc.append C (hacc C rfl)).intervals.getLast? = C.intervals.getLast? :=
      CertifiedZeroIntervals.append_getLast? _ _ _ (hne C (by simp))
    match r with
    | [] => simpa using hC
    | D :: t =>
      rcases hlast : (D :: t).getLast? with _ | E
      · simp at hlast
      · simp [hlast]
@[simp] theorem CertifiedZeroIntervals.join_intervals (l : List CertifiedZeroIntervals)
    (hne : ∀ C ∈ l, C.intervals ≠ []) (h : l.IsChain Separated) :
    (join l hne h).intervals = (l.map (·.intervals)).flatten := by
  cases l with
  | nil => simp [join, empty]
  | cons C r => simp [join, joinAux_intervals]
@[simp] theorem CertifiedZeroIntervals.join_getLast? (l : List CertifiedZeroIntervals)
    (hne : ∀ C ∈ l, C.intervals ≠ []) (h : l.IsChain Separated) :
    (join l hne h).intervals.getLast? = l.getLast?.bind (·.intervals.getLast?) := by
  cases l with
  | nil => simp [join, empty]
  | cons C r =>
    rw [join, joinAux_getLast?]
    match r with
    | [] => simp
    | D :: t =>
      rcases hlast : (D :: t).getLast? with _ | E
      · simp at hlast
      · simp [hlast]
end Zeta.Certificates
end
end CertificatePort133


section CertificatePort134
section
open Set
open scoped ComplexConjugate
theorem riemannZeta.le_N_of_zeros {T : ℝ} (Z : List ℂ)
    (hZ : ∀ s ∈ Z, s.im ∈ Ioo 0 T ∧ riemannZeta s = 0)
    (hZ_nodup : Z.Nodup) :
    Z.length ≤ riemannZeta.N T := by
  have hcard : Z.length ≤ Fintype.card ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T)) := by
    simpa using Fintype.card_le_of_injective
      (fun k : Fin Z.length ↦ (⟨Z.get k, Set.mem_univ _, (hZ _ (List.get_mem _ k)).1,
        (hZ _ (List.get_mem _ k)).2⟩ : ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T))))
      fun _ _ h ↦ List.nodup_iff_injective_get.mp hZ_nodup (congrArg Subtype.val h)
  rw [riemannZeta.N, riemannZeta.zeroes_sum, tsum_fintype]
  calc ((Z.length : ℕ) : ℝ)
      ≤ ∑ _ρ : ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T)), (1 : ℝ) := by
        simpa [Finset.card_univ] using (Nat.cast_le (α := ℝ)).2 hcard
    _ ≤ _ := Finset.sum_le_sum fun ρ _ ↦ by
        rw [one_mul]
        exact_mod_cast Kadiri.riemannZeta_one_le_order_positiveHeightZero ρ
theorem riemannZeta.ne_zero_of_re_ne_half_upto {s : ℂ} (Z : CertifiedZeroCount)
    (hs : s.im ∈ Ioo 0 (gramPoint Z.minIdx)) (hσ : s.re ≠ 1 / 2) :
    riemannZeta s ≠ 0 := by
  let n := Z.intervals.length
  have hN : riemannZeta.N (gramPoint Z.minIdx) = n := by
    apply le_antisymm
    · simp only [← Z.count, Nat.cast_add, Nat.cast_one, n]
      exact riemannZeta.N_le_of_certifiedGramBlockSeq Z.toCertifiedGramBlockSeq
    · simp only [n]
      grw [← riemannZeta.N_mono Z.below]
      exact riemannZeta.le_N_of_certifiedZeroIntervals Z.toCertifiedZeroIntervals
  intro hs_zero
  have : s ∉ Z.zeros := by grind [Z.zeros_re]
  let Z' := s::Z.zeros
  have := riemannZeta.le_N_of_zeros (T := gramPoint Z.minIdx) Z' (by
    simp only [List.mem_cons, forall_eq_or_imp, Z']
    refine ⟨⟨hs, hs_zero⟩, fun a ha ↦ ?_⟩
    refine ⟨Ioo_subset_Ioo le_rfl Z.below (Z.zeros_im ha), ?_⟩
    exact (Z.zeros_spec a ha).2) (by simp [Z', this, Z.zeros_nodup])
  simp [Z', Z.zeros_length] at this
  grind
def RiemannHypothesisUpTo (T : ℝ) : Prop :=
  ∀ s, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → |s.im| < T → s.re = 1/2
theorem riemannHypothesisUpTo (Z : CertifiedZeroCount) :
    RiemannHypothesisUpTo (gramPoint Z.minIdx) := by
  intro s h_zero h_non_trivial hs_one hs_im
  by_contra! hs_re
  rcases lt_trichotomy s.im 0 with (h_neg | h_eq | h_pos)
  · rw [abs_of_neg h_neg] at hs_im
    refine riemannZeta.ne_zero_of_re_ne_half_upto Z (s := conj s)
      (by simpa using ⟨h_neg, hs_im⟩) (by simpa using hs_re) ?_
    rw [riemannZeta_conj, h_zero, map_zero]
  · have := riemannZeta_ofReal_ne_zero (x := s.re)
    rw [← s.conj_eq_iff_re.1 <| s.conj_eq_iff_im.2 h_eq] at h_non_trivial h_zero
    aesop
  · rw [abs_of_nonneg h_pos.le] at hs_im
    exact riemannZeta.ne_zero_of_re_ne_half_upto Z ⟨h_pos, hs_im⟩ hs_re h_zero
open Zeta.Certificates in
theorem riemannHypothesisUpTo_of_batchSpec {n an ad bn bd : ℕ} (G : CertifiedGramBlockSeq)
    (h : BatchSpec n an ad bn bd) (hcount : G.minIdx + 1 = n)
    (hbelow : Enclosure.sfrac false bn bd ≤ gramPoint G.minIdx) :
    RiemannHypothesisUpTo (gramPoint G.minIdx) :=
  riemannHypothesisUpTo
    { toCertifiedGramBlockSeq := G
      toCertifiedZeroIntervals := h.bundle
      count := by rw [h.bundle_length]; exact hcount
      below := h.bundle.height_le_of_getLast?_snd h.bundle_getLast? hbelow }
end
end CertificatePort134


section CertificatePort135
section
open scoped Nat
namespace TangentNumbers
noncomputable section
section Poly
open Polynomial
def tangentPoly : ℕ → ℕ[X]
  | 0 => X
  | (n + 1) => (1 + X ^ 2) * derivative (tangentPoly n)
lemma tangentPoly_succ (n : ℕ) :
    tangentPoly (n + 1) = (1 + X ^ 2) * derivative (tangentPoly n) :=
  rfl
def tangentNumber (n : ℕ) : ℕ :=
  (tangentPoly (2 * n - 1)).eval 0
def tanhPoly : ℕ → ℤ[X]
  | 0 => .X
  | (n + 1) => (1 - .X ^ 2 : ℤ[X]) * .derivative (tanhPoly n)
private lemma tanhPoly_succ (n : ℕ) :
    tanhPoly (n + 1) = (1 - .X ^ 2 : ℤ[X]) * .derivative (tanhPoly n) :=
  rfl
open Complex
private lemma map_tanhPoly (n : ℕ) :
    (tanhPoly n).map (algebraMap ℤ ℂ) =
      C (-I ^ (n + 1)) *
        ((tangentPoly n).map (algebraMap ℕ ℂ)).comp (C I * X) := by
  induction n with
  | zero =>
    simp only [tanhPoly, tangentPoly, map_X, X_comp, zero_add, pow_one]
    rw [← mul_assoc, ← C_mul, neg_mul, I_mul_I]
    simp
  | succ n ih =>
    have hCI : C I ^ 2 = -1 := by
      rw [← C_pow, I_sq, C_neg, C_1]
    have hI : C (-I ^ (n + 2)) = C (-I ^ (n + 1)) * C I := by
      grind [C_mul, pow_succ]
    rw [tanhPoly_succ, tangentPoly_succ]
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one,
      Polynomial.map_pow, map_X, ← derivative_map, ih, derivative_comp, derivative_mul,
      derivative_C, derivative_X, mul_comp, add_comp, one_comp, pow_comp, X_comp]
    grind
end Poly
section PowerSeries
open PowerSeries
section ForMathlib
private lemma coeff_iterate_derivative {R : Type*} [CommRing R] (f : R⟦X⟧) (n k : ℕ) :
    coeff k ((d⁄dX R)^[n] f) = (k + 1).ascFactorial n * coeff (k + n) f := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', coeff_derivative, ih, Nat.ascFactorial_succ,
      ← Nat.succ_ascFactorial]
    grind
private lemma coeff_zero_iterate {R : Type*} [CommRing R] (f : R⟦X⟧) (n : ℕ) :
    coeff 0 ((d⁄dX R)^[n] f) = n ! * coeff n f := by simpa using coeff_iterate_derivative f n 0
end ForMathlib
def tanhSeries : ℚ⟦X⟧ :=
  (exp ℚ ^ 2 - 1) * (exp ℚ ^ 2 + 1)⁻¹
private lemma tanhSeries_mul_expSq_add_one :
    tanhSeries * (exp ℚ ^ 2 + 1) = exp ℚ ^ 2 - 1 := by
  simp [tanhSeries, mul_assoc, PowerSeries.inv_mul_cancel]
lemma ne_zero_of_coeff_ne_zero {R : Type*} [Semiring R] {p : R⟦X⟧} (n : ℕ) (h : p.coeff n ≠ 0) :
    p ≠ 0 := by
  grind
private lemma expSq_add_one_ne_zero : exp ℚ ^ 2 + 1 ≠ 0 :=
  ne_zero_of_coeff_ne_zero 0 (by simp)
private lemma constantCoeff_tanhSeries : constantCoeff tanhSeries = 0 := by simp [tanhSeries]
private lemma derivative_tanhSeries :
    d⁄dX ℚ tanhSeries = 1 - tanhSeries ^ 2 := by
  have hd : tanhSeries * (2 * (exp ℚ * exp ℚ)) + (exp ℚ ^ 2 + 1) * d⁄dX ℚ tanhSeries =
      2 * (exp ℚ * exp ℚ) := by
    simpa [derivative_exp] using congr(d⁄dX ℚ $tanhSeries_mul_expSq_add_one)
  refine mul_left_cancel₀ expSq_add_one_ne_zero ?_
  linear_combination hd - (1 - tanhSeries) * tanhSeries_mul_expSq_add_one
open scoped Polynomial
private lemma aeval_tanhSeries_map (p : ℤ[X]) :
    Polynomial.aeval tanhSeries (p.map (algebraMap ℤ ℚ)) = Polynomial.aeval tanhSeries p :=
  (Polynomial.aeval_eq_aeval_map (by ext; simp) p tanhSeries).symm
private lemma iterate_derivative_tanhSeries (n : ℕ) :
    (d⁄dX ℚ)^[n] tanhSeries = (tanhPoly n).aeval tanhSeries := by
  induction n with
  | zero => simp [tanhPoly]
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, ← aeval_tanhSeries_map (tanhPoly n), Derivation.map_aeval, derivative_tanhSeries,
      smul_eq_mul, Polynomial.derivative_map, aeval_tanhSeries_map, tanhPoly_succ]
    simp
    ring
private lemma constantCoeff_aeval_tanhSeries (p : ℤ[X]) :
    constantCoeff (p.aeval tanhSeries) = p.eval 0 := by
  induction p using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a _ => simp [map_mul, map_pow, constantCoeff_tanhSeries]
private lemma eval_tanhPoly (n : ℕ) :
    (tanhPoly n).eval 0 = n ! * coeff n tanhSeries := by
  rw [← constantCoeff_aeval_tanhSeries, ← coeff_zero_eq_constantCoeff_apply,
    ← iterate_derivative_tanhSeries n, coeff_zero_iterate]
private lemma eval_zero_map {R S : Type*} [CommSemiring R] [Semiring S] (f : R →+* S) (p : R[X]) :
    (p.map f).eval 0 = f (p.eval 0) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
      Polynomial.coeff_zero_eq_eval_zero]
private lemma eval_tangentPoly (m : ℕ) :
    (tangentPoly (2 * m + 1)).eval 0 = (-1) ^ m * (2 * m + 1)! * coeff (2 * m + 1) tanhSeries := by
  have hmap := congrArg (Polynomial.eval 0) (map_tanhPoly (2 * m + 1))
  have hI : -Complex.I ^ (2 * m + 2) = (-1) ^ m := by
    have he : 2 * m + 2 = 2 * (m + 1) := by ring
    rw [he, pow_mul, Complex.I_sq]
    ring
  simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_X,
    mul_zero, eval_zero_map, eq_intCast, eq_natCast, hI] at hmap
  have hq : (tanhPoly (2 * m + 1)).eval 0
      = (-1) ^ m * (((tangentPoly (2 * m + 1)).eval 0 : ℕ) : ℚ) := mod_cast hmap
  rw [eval_tanhPoly] at hq
  rw [mul_assoc, hq, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨m, rfl⟩, one_mul]
section
variable {R : Type*} [Semiring R] {p : R⟦X⟧}
@[simp] lemma coeff_mul_natCast {a k : ℕ} :
    coeff k (p * a : R⟦X⟧) = coeff k p * a := coeff_mul_C _ _ _
@[simp] lemma coeff_natCast_mul {a k : ℕ} :
    coeff k (a * p : R⟦X⟧) = a * coeff k p := coeff_C_mul _ _ _
@[simp] lemma coeff_mul_ofNat {a k : ℕ} [Nat.AtLeastTwo a] :
    coeff k (p * (ofNat(a) : R⟦X⟧)) = coeff k p * ofNat(a) := coeff_mul_C _ _ _
@[simp] lemma coeff_ofNat_mul {a k : ℕ} [Nat.AtLeastTwo a] :
    coeff k ((ofNat(a) : R⟦X⟧) * p) = ofNat(a) * coeff k p := coeff_C_mul _ _ _
end
theorem coeff_tanhSeries (m : ℕ) :
    coeff (2 * m + 1) tanhSeries =
      2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1) * bernoulli (2 * m + 2) / (2 * m + 2)! := by
  set D := bernoulliPowerSeries ℚ + bernoulli'PowerSeries ℚ with hD
  have hcoeffD : coeff (2 * m + 2) D = 2 * bernoulli (2 * m + 2) / (2 * m + 2)! := by
    simp [hD, map_add, bernoulliPowerSeries, bernoulli'PowerSeries]
    grind [bernoulli_eq_bernoulli'_of_ne_one]
  have main : 2 * X * tanhSeries = rescale 4 D - rescale 2 D := by
    have B3 : D * (exp ℚ - 1) = .X * (exp ℚ + 1) := by
      rw [hD, add_mul, bernoulliPowerSeries_mul_exp_sub_one,
        bernoulli'PowerSeries_mul_exp_sub_one]
      grind
    have h2 : rescale 2 D * (exp ℚ ^ 2 - 1) = 2 * .X * (exp ℚ ^ 2 + 1) := by
      simpa [exp_pow_eq_rescale_exp, map_ofNat] using congrArg (rescale 2) B3
    have h4 : rescale 4 D * (exp ℚ ^ 4 - 1) = 4 * .X * (exp ℚ ^ 4 + 1) := by
      simpa [exp_pow_eq_rescale_exp, map_ofNat] using congrArg (rescale 4) B3
    have hP : (exp ℚ ^ 2 + 1) * (exp ℚ ^ 2 - 1) ≠ 0 := by
      apply mul_ne_zero <;>
      · apply ne_zero_of_coeff_ne_zero 1
        simp [exp_pow_eq_rescale_exp]
    apply mul_right_cancel₀ hP
    linear_combination (2 * X * (exp ℚ ^ 2 - 1)) * tanhSeries_mul_expSq_add_one - h4 +
      (exp ℚ ^ 2 + 1) * h2
  have hcoeff := congrArg (coeff (2 * m + 2)) main
  have lhs : coeff (2 * m + 2) (X * (2 • tanhSeries)) = 2 * coeff (2 * m + 1) tanhSeries := by simp
  have rhs : coeff (2 * m + 2) (rescale 4 D - rescale 2 D) =
      (4 ^ (2 * m + 2) - 2 ^ (2 * m + 2)) * coeff (2 * m + 2) D := by grind [coeff_rescale]
  have h4eq : (4 ^ (2 * m + 2) : ℚ) = (2 ^ (2 * m + 2)) ^ 2 := by
    have : (4 : ℚ) = 2 ^ 2 := by norm_num
    rw [this, pow_right_comm]
  grind
theorem tangentNumber_eq (m : ℕ) :
    tangentNumber (m + 1) =
      (-1) ^ m * (2 * m + 1)! *
        2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1) * bernoulli (2 * m + 2) / (2 * m + 2)! := by
  grind [tangentNumber, eval_tangentPoly, coeff_tanhSeries]
end PowerSeries
end
end TangentNumbers
end
end CertificatePort135
theorem TangentNumbers.tangentNumberLit_1 : TangentNumbers.tangentNumber 1 = 1 := by
  simp [TangentNumbers.tangentNumber, TangentNumbers.tangentPoly]
theorem TangentNumbers.tangentNumberLit_2 : TangentNumbers.tangentNumber 2 = 2 := by
  simp [TangentNumbers.tangentNumber, TangentNumbers.tangentPoly]


section CertificatePort138
section
open scoped Nat
namespace TangentNumbers
theorem num_eq_of_eq_intDiv {A B p q : ℤ} (hB : B ≠ 0) (hq : 0 < q)
    (hcop : Int.gcd p q = 1) (hcross : p * B = q * A) :
    ((A : ℚ) / (B : ℚ)).num = p := by
  have heq : (A : ℚ) / (B : ℚ) = (p : ℚ) / (q : ℚ) := by
    rw [div_eq_div_iff (by exact_mod_cast hB) (by exact_mod_cast hq.ne')]
    have : A * q = p * B := by linear_combination -hcross
    exact_mod_cast this
  rw [heq]
  exact Rat.num_div_eq_of_coprime hq hcop
open PowerSeries in
theorem bernoulli_eq_tangent_intDiv (m : ℕ) :
    bernoulli (2 * m + 2) =
      (((-1) ^ m * (2 * m + 2) * (tangentNumber (m + 1) : ℤ) : ℤ) : ℚ) /
        (((2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1) : ℤ) : ℚ)) := by
  have h := tangentNumber_eq m
  have hfac : ((2 * m + 2)! : ℚ) = (2 * m + 2) * (2 * m + 1)! := by
    have hidx : 2 * m + 2 = (2 * m + 1) + 1 := rfl
    rw [hidx, Nat.factorial_succ]
    push_cast
    ring
  have hP : (2 : ℚ) ^ (2 * m + 2) ≠ 0 := by positivity
  have hQ : (2 : ℚ) ^ (2 * m + 2) - 1 ≠ 0 := by
    have h1 : (1 : ℚ) < 2 ^ (2 * m + 2) := one_lt_pow₀ (by norm_num) (by positivity)
    linarith
  have hfac' : ((2 * m + 1)! : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [hfac] at h
  push_cast at h ⊢
  rw [h]
  field_simp
  have hs : (((-1 : ℚ)) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [hs, mul_one]
theorem intDenom_ne_zero (m : ℕ) : (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1) : ℤ) ≠ 0 :=
  mul_ne_zero (by positivity) (sub_ne_zero.mpr (one_lt_pow₀ (by norm_num) (by omega)).ne')
theorem bernoulli_num_of (m : ℕ) (Tn : ℕ) (p q : ℤ)
    (hT : tangentNumber (m + 1) = Tn)
    (hq : decide (0 < q) = true)
    (hcop : (Int.gcd p q).beq 1 = true)
    (hcross : decide (p * (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1))
                = q * ((-1) ^ m * (2 * m + 2) * (Tn : ℤ))) = true) :
    (bernoulli (2 * m + 2)).num = p := by
  have hq' : 0 < q := of_decide_eq_true hq
  have hcop' : Int.gcd p q = 1 := Nat.eq_of_beq_eq_true hcop
  have hcross' : p * (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1))
      = q * ((-1) ^ m * (2 * m + 2) * (Tn : ℤ)) := of_decide_eq_true hcross
  have hTn : (tangentNumber (m + 1) : ℤ) = (Tn : ℤ) := by rw [hT]
  rw [bernoulli_eq_tangent_intDiv m, hTn]
  exact num_eq_of_eq_intDiv (intDenom_ne_zero m) hq' hcop' hcross'
theorem numAbs_of (m n : ℕ) (p : ℤ) (hnum : (bernoulli (2 * m + 2)).num = p)
    (hn : p.natAbs.beq n = true) : (bernoulli (2 * m + 2)).num.natAbs = n := by
  rw [hnum]; exact Nat.eq_of_beq_eq_true hn
end TangentNumbers
end
end CertificatePort138


section CertificatePort139
section
namespace BSN
def binarySplit (p q : Nat → Nat) (m n : Nat) : Nat × Nat × Nat :=
  if _h : m < n then
    if _h2 : m + 1 = n then (p m, q m, p m)
    else
      let (tl, ql, pl) := binarySplit p q m ((m + n) / 2)
      let (tr, qr, pr) := binarySplit p q ((m + n) / 2) n
      (tl * qr + pl * tr, ql * qr, pl * pr)
  else (0, 1, 1)
termination_by n - m
decreasing_by all_goals omega
def cosEvenP (u : Nat) : Nat → Nat := fun _ => Nat.pow u 4
def cosEvenQ (v : Nat) : Nat → Nat := fun k =>
  Nat.mul (Nat.pow v 4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.succ (Nat.mul 4 k)) (Nat.add (Nat.mul 4 k) 2))
      (Nat.add (Nat.mul 4 k) 3)) (Nat.add (Nat.mul 4 k) 4))
def cosOddP (u : Nat) : Nat → Nat := fun _ => Nat.pow u 4
def cosOddQ (v : Nat) : Nat → Nat := fun k =>
  Nat.mul (Nat.pow v 4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.add (Nat.mul 4 k) 3) (Nat.add (Nat.mul 4 k) 4))
      (Nat.add (Nat.mul 4 k) 5)) (Nat.add (Nat.mul 4 k) 6))
def sinEvenP (u : Nat) : Nat → Nat := fun _ => Nat.pow u 4
def sinEvenQ (v : Nat) : Nat → Nat := fun k =>
  Nat.mul (Nat.pow v 4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.add (Nat.mul 4 k) 2) (Nat.add (Nat.mul 4 k) 3))
      (Nat.add (Nat.mul 4 k) 4)) (Nat.add (Nat.mul 4 k) 5))
def sinOddP (u : Nat) : Nat → Nat := fun _ => Nat.pow u 4
def sinOddQ (v : Nat) : Nat → Nat := fun k =>
  Nat.mul (Nat.pow v 4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.add (Nat.mul 4 k) 4) (Nat.add (Nat.mul 4 k) 5))
      (Nat.add (Nat.mul 4 k) 6)) (Nat.add (Nat.mul 4 k) 7))
def artanhP (u : Nat) : Nat
    → Nat := fun k => Nat.mul (Nat.pow u (nat_lit 2)) (Nat.succ (Nat.mul (nat_lit 2) k))
def artanhQ (v : Nat) : Nat
    → Nat := fun k => Nat.mul (Nat.pow v (nat_lit 2)) (Nat.add (Nat.mul (nat_lit 2) k) (nat_lit 3))
def arctanEvenP (u : Nat) : Nat → Nat := fun k => Nat.mul (Nat.pow u 4) (Nat.succ (Nat.mul 4 k))
def arctanEvenQ (v : Nat) : Nat → Nat := fun k => Nat.mul (Nat.pow v 4) (Nat.add (Nat.mul 4 k) 5)
def arctanOddP (u : Nat) : Nat → Nat := fun k => Nat.mul (Nat.pow u 4) (Nat.add (Nat.mul 4 k) 3)
def arctanOddQ (v : Nat) : Nat → Nat := fun k => Nat.mul (Nat.pow v 4) (Nat.add (Nat.mul 4 k) 7)
end BSN
end
end CertificatePort139


section CertificatePort140
section
namespace BSN
open Enclosure
open Finset
theorem binarySplit_PQ {p q : ℕ → ℕ} {m n : ℕ} :
    (binarySplit p q m n).2.2 = ∏ j ∈ Ico m n, p j ∧
    (binarySplit p q m n).2.1 = ∏ j ∈ Ico m n, q j := by
  fun_induction binarySplit with
  | case1 m hlt => simp [Nat.Ico_succ_singleton]
  | case3 m n => simp_all
  | case2 m n hlt hne tl ql pl hL tr qr pr hR ihL ihR =>
    simp only [hL] at ihL; simp only [hR] at ihR
    have hmk : m ≤ (m + n) / 2 := by omega
    have hkn : (m + n) / 2 ≤ n := by omega
    refine ⟨?_, ?_⟩ <;>
      rw [← prod_Ico_consecutive _ hmk hkn] <;> simp [ihL.1, ihL.2, ihR.1, ihR.2]
theorem binarySplit_nonzero {p q : ℕ → ℕ} {m n : ℕ} (hq : ∀ i, q i ≠ 0) :
    (binarySplit p q m n).2.1 ≠ 0 := by
  fun_induction binarySplit <;> simp_all
theorem binarySplit_spec {p q : ℕ → ℕ} {m n T Q P : ℕ} (hq : ∀ i, q i ≠ 0)
    (h : (T, Q, P) = binarySplit p q m n) :
    (∏ j ∈ Ico m n, ((p j : ℚ) / q j) = (P : ℚ) / Q) ∧
    (∑ i ∈ Ico m n, ∏ j ∈ Ico m (i + 1), ((p j : ℚ) / q j) = (T : ℚ) / Q) := by
  fun_induction binarySplit generalizing T Q P with
  | case1 m hlt =>
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hIco : Finset.Ico m (m + 1) = {m} := by
      ext x; rw [Finset.mem_Ico, Finset.mem_singleton]; omega
    simp [hIco]
  | case3 m n =>
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [Ico_eq_empty (by omega : ¬ m < n)]
  | case2 m n hlt hne tl ql pl hL tr qr pr hR ihL ihR =>
    specialize ihL hL.symm; specialize ihR hR.symm
    have hmk : m ≤ (m + n) / 2 := by omega
    have hkn : (m + n) / 2 ≤ n := by omega
    obtain ⟨hPl, hSl⟩ := ihL
    obtain ⟨hPr, hSr⟩ := ihR
    obtain ⟨hPpl, hQl⟩ := (binarySplit_PQ (p := p) (q := q) (m := m) (n := (m + n) / 2))
    simp only [hL] at hPpl hQl
    obtain ⟨hPpr, hQr⟩ := (binarySplit_PQ (p := p) (q := q) (m := (m + n) / 2) (n := n))
    simp only [hR] at hPpr hQr
    have hqtl := binarySplit_nonzero (p := p) (m := m) (n := (m + n) / 2) hq
    simp only [hL] at hqtl
    have hqtr := binarySplit_nonzero (p := p) (m := (m + n) / 2) (n := n) hq
    simp only [hR] at hqtr
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hqlr : (ql : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hqtl
    have hqrr : (qr : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hqtr
    constructor
    · rw [← prod_Ico_consecutive _ hmk hkn, hPl, hPr]; push_cast; field_simp
    · rw [← sum_Ico_consecutive _ hmk hkn, hSl]
      have hsplit : ∑ i ∈ Ico ((m + n) / 2) n, ∏ j ∈ Ico m (i + 1), ((p j : ℚ) / q j)
          = ((pl : ℚ) / ql) * ∑ i ∈ Ico ((m + n) / 2) n, ∏ j ∈ Ico ((m + n) / 2) (i + 1),
              ((p j : ℚ) / q j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [Finset.mem_Ico] at hi
        rw [← prod_Ico_consecutive _ hmk (by omega : (m + n) / 2 ≤ i + 1), hPl]
      rw [hsplit, hSr]
      push_cast
      field_simp
theorem Nat.div_eq' {a b : ℕ} : a.div b = a / b := rfl
theorem binarySplit_of_le {p q : ℕ → ℕ} {m n : ℕ} (h : n.ble m) :
    binarySplit p q m n = (0, 1, 1) := by
  rw [binarySplit]; simp only [Nat.ble_eq] at h; rw [dif_neg (by omega)]
theorem binarySplit_of_base {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.succ).beq n) (hT : T.beq (p m)) (hQ : Q.beq (q m)) (hP : P.beq (p m)) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  rw [binarySplit, dif_pos (by omega), dif_pos rfl]
theorem binarySplit_rec {p q : ℕ → ℕ}
    {m n k tl ql pl tr qr pr T Q P : ℕ}
    (h1 : (m.succ).blt n) (hk : k.beq ((m.add n).div 2))
    (hT : T.beq ((tl.mul qr).add (pl.mul tr))) (hQ : Q.beq (ql.mul qr))
    (hP : P.beq (pl.mul pr))
    (hl : binarySplit p q m k = (tl, ql, pl))
    (hr : binarySplit p q k n = (tr, qr, pr)) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.blt_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.div_eq'] at h1 hk hT hQ hP
  subst hk hT hQ hP
  rw [binarySplit, dif_pos (by omega), dif_neg (by omega), hl, hr]
theorem binarySplit_of_base2 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 2).beq n)
    (hT : T.beq (((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))))
    (hQ : Q.beq ((q m).mul (q (m.succ))))
    (hP : P.beq ((p m).mul (p (m.succ)))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 1) = (p m, q m, p m) :=
    binarySplit_of_base (by simp) (by simp) (by simp) (by simp)
  have hr : binarySplit p q (m + 1) (m + 2) = (p (m + 1), q (m + 1), p (m + 1)) :=
    binarySplit_of_base (by simp) (by simp) (by simp) (by simp)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base3 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 3).beq n)
    (hT : T.beq (((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add
      ((p m).mul (((p (m.succ)).mul (q (m.add 2))).add
        ((p (m.succ)).mul (p (m.add 2)))))))
    (hQ : Q.beq ((q m).mul ((q (m.succ)).mul (q (m.add 2)))))
    (hP : P.beq ((p m).mul ((p (m.succ)).mul (p (m.add 2))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 1) = (p m, q m, p m) :=
    binarySplit_of_base (by simp) (by simp) (by simp) (by simp)
  have hr : binarySplit p q (m + 1) (m + 3) =
      (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2), q (m + 1) * q (m + 2),
        p (m + 1) * p (m + 2)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base4 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 4).beq n)
    (hT : T.beq (((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul
        ((q (m.add 2)).mul (q (m.add 3)))).add
      (((p m).mul (p (m.succ))).mul
        (((p (m.add 2)).mul (q (m.add 3))).add ((p (m.add 2)).mul (p (m.add 3)))))))
    (hQ : Q.beq (((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul (q (m.add 3)))))
    (hP : P.beq (((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 2) =
      (p m * q (m + 1) + p m * p (m + 1), q m * q (m + 1), p m * p (m + 1)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 2) (m + 4) =
      (p (m + 2) * q (m + 3) + p (m + 2) * p (m + 3), q (m + 2) * q (m + 3),
        p (m + 2) * p (m + 3)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base5 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 5).beq n)
    (hT : T.beq (((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add 2)).mul
        ((q (m.add 3)).mul (q (m.add 4))))).add (((p m).mul (p (m.succ))).mul (((p (m.add 2)).mul
        ((q (m.add 3)).mul (q (m.add 4)))).add ((p (m.add 2)).mul (((p (m.add 3)).mul (q (m.add
        4))).add ((p (m.add 3)).mul (p (m.add 4)))))))))
    (hQ : Q.beq (((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul ((q (m.add 3)).mul (q (m.add
        4))))))
    (hP : P.beq (((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul ((p (m.add 3)).mul (p (m.add
        4)))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 2) =
      (p m * q (m + 1) + p m * p (m + 1), q m * q (m + 1), p m * p (m + 1)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 2) (m + 5) =
      (p (m + 2) * (q (m + 3) * q (m + 4)) + p (m + 2) * (p (m + 3) * q (m + 4) + p (m + 3) * p (m
          + 4)), q (m + 2) * (q (m + 3) * q (m + 4)), p (m + 2) * (p (m + 3) * p (m + 4))) :=
    binarySplit_of_base3 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base6 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 6).beq n)
    (hT : T.beq (((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul ((q (m.add 3)).mul ((q
        (m.add 4)).mul (q (m.add 5))))).add (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul
        (((p (m.add 3)).mul ((q (m.add 4)).mul (q (m.add 5)))).add ((p (m.add 3)).mul (((p (m.add
        4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add 5)))))))))
    (hQ : Q.beq (((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul ((q (m.add 3)).mul ((q (m.add
        4)).mul (q (m.add 5))))))
    (hP : P.beq (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p (m.add 3)).mul ((p (m.add
        4)).mul (p (m.add 5)))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 3) =
      (p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2)), q m
          * (q (m + 1) * q (m + 2)), p m * (p (m + 1) * p (m + 2))) :=
    binarySplit_of_base3 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 3) (m + 6) =
      (p (m + 3) * (q (m + 4) * q (m + 5)) + p (m + 3) * (p (m + 4) * q (m + 5) + p (m + 4) * p (m
          + 5)), q (m + 3) * (q (m + 4) * q (m + 5)), p (m + 3) * (p (m + 4) * p (m + 5))) :=
    binarySplit_of_base3 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base7 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 7).beq n)
    (hT : T.beq (((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul (((q (m.add 3)).mul (q
        (m.add 4))).mul ((q (m.add 5)).mul (q (m.add 6))))).add (((p m).mul ((p (m.succ)).mul (p
        (m.add 2)))).mul (((((p (m.add 3)).mul (q (m.add 4))).add ((p (m.add 3)).mul (p (m.add
        4)))).mul ((q (m.add 5)).mul (q (m.add 6)))).add (((p (m.add 3)).mul (p (m.add 4))).mul
        (((p (m.add 5)).mul (q (m.add 6))).add ((p (m.add 5)).mul (p (m.add 6)))))))))
    (hQ : Q.beq (((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul (((q (m.add 3)).mul (q (m.add
        4))).mul ((q (m.add 5)).mul (q (m.add 6))))))
    (hP : P.beq (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul (((p (m.add 3)).mul (p (m.add
        4))).mul ((p (m.add 5)).mul (p (m.add 6)))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 3) =
      (p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2)), q m
          * (q (m + 1) * q (m + 2)), p m * (p (m + 1) * p (m + 2))) :=
    binarySplit_of_base3 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 3) (m + 7) =
      ((p (m + 3) * q (m + 4) + p (m + 3) * p (m + 4)) * (q (m + 5) * q (m + 6)) + p (m + 3) * p
          (m + 4) * (p (m + 5) * q (m + 6) + p (m + 5) * p (m + 6)), q (m + 3) * q (m + 4) * (q (m
          + 5) * q (m + 6)), p (m + 3) * p (m + 4) * (p (m + 5) * p (m + 6))) :=
    binarySplit_of_base4 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base8 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 8).beq n)
    (hT : T.beq (((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul (q (m.add 3)))).add (((p m).mul (p (m.succ))).mul (((p (m.add 2)).mul (q (m.add
        3))).add ((p (m.add 2)).mul (p (m.add 3)))))).mul (((q (m.add 4)).mul (q (m.add 5))).mul
        ((q (m.add 6)).mul (q (m.add 7))))).add ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul
        (p (m.add 3)))).mul (((((p (m.add 4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add
        5)))).mul ((q (m.add 6)).mul (q (m.add 7)))).add (((p (m.add 4)).mul (p (m.add 5))).mul
        (((p (m.add 6)).mul (q (m.add 7))).add ((p (m.add 6)).mul (p (m.add 7)))))))))
    (hQ : Q.beq ((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul (q (m.add 3)))).mul (((q (m.add
        4)).mul (q (m.add 5))).mul ((q (m.add 6)).mul (q (m.add 7))))))
    (hP : P.beq ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((p (m.add
        4)).mul (p (m.add 5))).mul ((p (m.add 6)).mul (p (m.add 7)))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 4) =
      ((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * q (m + 3)) + p m * p (m + 1) * (p (m +
          2) * q (m + 3) + p (m + 2) * p (m + 3)), q m * q (m + 1) * (q (m + 2) * q (m + 3)), p m
          * p (m + 1) * (p (m + 2) * p (m + 3))) :=
    binarySplit_of_base4 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 4) (m + 8) =
      ((p (m + 4) * q (m + 5) + p (m + 4) * p (m + 5)) * (q (m + 6) * q (m + 7)) + p (m + 4) * p
          (m + 5) * (p (m + 6) * q (m + 7) + p (m + 6) * p (m + 7)), q (m + 4) * q (m + 5) * (q (m
          + 6) * q (m + 7)), p (m + 4) * p (m + 5) * (p (m + 6) * p (m + 7))) :=
    binarySplit_of_base4 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base9 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 9).beq n)
    (hT : T.beq (((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul (q (m.add 3)))).add (((p m).mul (p (m.succ))).mul (((p (m.add 2)).mul (q (m.add
        3))).add ((p (m.add 2)).mul (p (m.add 3)))))).mul (((q (m.add 4)).mul (q (m.add 5))).mul
        ((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add 8)))))).add ((((p m).mul (p (m.add
        1))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((((p (m.add 4)).mul (q (m.add 5))).add
        ((p (m.add 4)).mul (p (m.add 5)))).mul ((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add
        8))))).add (((p (m.add 4)).mul (p (m.add 5))).mul (((p (m.add 6)).mul ((q (m.add 7)).mul
        (q (m.add 8)))).add ((p (m.add 6)).mul (((p (m.add 7)).mul (q (m.add 8))).add ((p (m.add
        7)).mul (p (m.add 8)))))))))))
    (hQ : Q.beq ((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul (q (m.add 3)))).mul (((q (m.add
        4)).mul (q (m.add 5))).mul ((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add 8)))))))
    (hP : P.beq ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((p (m.add
        4)).mul (p (m.add 5))).mul ((p (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 4) =
      ((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * q (m + 3)) + p m * p (m + 1) * (p (m +
          2) * q (m + 3) + p (m + 2) * p (m + 3)), q m * q (m + 1) * (q (m + 2) * q (m + 3)), p m
          * p (m + 1) * (p (m + 2) * p (m + 3))) :=
    binarySplit_of_base4 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 4) (m + 9) =
      ((p (m + 4) * q (m + 5) + p (m + 4) * p (m + 5)) * (q (m + 6) * (q (m + 7) * q (m + 8))) + p
          (m + 4) * p (m + 5) * (p (m + 6) * (q (m + 7) * q (m + 8)) + p (m + 6) * (p (m + 7) * q
          (m + 8) + p (m + 7) * p (m + 8))), q (m + 4) * q (m + 5) * (q (m + 6) * (q (m + 7) * q
          (m + 8))), p (m + 4) * p (m + 5) * (p (m + 6) * (p (m + 7) * p (m + 8)))) :=
    binarySplit_of_base5 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base10 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 10).beq n)
    (hT : T.beq (((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul ((q (m.add 3)).mul (q (m.add 4))))).add (((p m).mul (p (m.succ))).mul (((p (m.add
        2)).mul ((q (m.add 3)).mul (q (m.add 4)))).add ((p (m.add 2)).mul (((p (m.add 3)).mul (q
        (m.add 4))).add ((p (m.add 3)).mul (p (m.add 4)))))))).mul (((q (m.add 5)).mul (q (m.add
        6))).mul ((q (m.add 7)).mul ((q (m.add 8)).mul (q (m.add 9)))))).add ((((p m).mul (p
        (m.succ))).mul ((p (m.add 2)).mul ((p (m.add 3)).mul (p (m.add 4))))).mul (((((p (m.add
        5)).mul (q (m.add 6))).add ((p (m.add 5)).mul (p (m.add 6)))).mul ((q (m.add 7)).mul ((q
        (m.add 8)).mul (q (m.add 9))))).add (((p (m.add 5)).mul (p (m.add 6))).mul (((p (m.add
        7)).mul ((q (m.add 8)).mul (q (m.add 9)))).add ((p (m.add 7)).mul (((p (m.add 8)).mul (q
        (m.add 9))).add ((p (m.add 8)).mul (p (m.add 9)))))))))))
    (hQ : Q.beq ((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul ((q (m.add 3)).mul (q (m.add
        4))))).mul (((q (m.add 5)).mul (q (m.add 6))).mul ((q (m.add 7)).mul ((q (m.add 8)).mul (q
        (m.add 9)))))))
    (hP : P.beq ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul ((p (m.add 3)).mul (p (m.add
        4))))).mul (((p (m.add 5)).mul (p (m.add 6))).mul ((p (m.add 7)).mul ((p (m.add 8)).mul (p
        (m.add 9))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 5) =
      ((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * (q (m + 3) * q (m + 4))) + p m * p (m +
          1) * (p (m + 2) * (q (m + 3) * q (m + 4)) + p (m + 2) * (p (m + 3) * q (m + 4) + p (m +
          3) * p (m + 4))), q m * q (m + 1) * (q (m + 2) * (q (m + 3) * q (m + 4))), p m * p (m +
          1) * (p (m + 2) * (p (m + 3) * p (m + 4)))) :=
    binarySplit_of_base5 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 5) (m + 10) =
      ((p (m + 5) * q (m + 6) + p (m + 5) * p (m + 6)) * (q (m + 7) * (q (m + 8) * q (m + 9))) + p
          (m + 5) * p (m + 6) * (p (m + 7) * (q (m + 8) * q (m + 9)) + p (m + 7) * (p (m + 8) * q
          (m + 9) + p (m + 8) * p (m + 9))), q (m + 5) * q (m + 6) * (q (m + 7) * (q (m + 8) * q
          (m + 9))), p (m + 5) * p (m + 6) * (p (m + 7) * (p (m + 8) * p (m + 9)))) :=
    binarySplit_of_base5 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base11 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 11).beq n)
    (hT : T.beq (((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul ((q (m.add 3)).mul (q (m.add 4))))).add (((p m).mul (p (m.succ))).mul (((p (m.add
        2)).mul ((q (m.add 3)).mul (q (m.add 4)))).add ((p (m.add 2)).mul (((p (m.add 3)).mul (q
        (m.add 4))).add ((p (m.add 3)).mul (p (m.add 4)))))))).mul (((q (m.add 5)).mul ((q (m.add
        6)).mul (q (m.add 7)))).mul ((q (m.add 8)).mul ((q (m.add 9)).mul (q (m.add 10)))))).add
        ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul ((p (m.add 3)).mul (p (m.add 4))))).mul
        (((((p (m.add 5)).mul ((q (m.add 6)).mul (q (m.add 7)))).add ((p (m.add 5)).mul (((p
        (m.add 6)).mul (q (m.add 7))).add ((p (m.add 6)).mul (p (m.add 7)))))).mul ((q (m.add
        8)).mul ((q (m.add 9)).mul (q (m.add 10))))).add (((p (m.add 5)).mul ((p (m.add 6)).mul (p
        (m.add 7)))).mul (((p (m.add 8)).mul ((q (m.add 9)).mul (q (m.add 10)))).add ((p (m.add
        8)).mul (((p (m.add 9)).mul (q (m.add 10))).add ((p (m.add 9)).mul (p (m.add 10)))))))))))
    (hQ : Q.beq ((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul ((q (m.add 3)).mul (q (m.add
        4))))).mul (((q (m.add 5)).mul ((q (m.add 6)).mul (q (m.add 7)))).mul ((q (m.add 8)).mul
        ((q (m.add 9)).mul (q (m.add 10)))))))
    (hP : P.beq ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul ((p (m.add 3)).mul (p (m.add
        4))))).mul (((p (m.add 5)).mul ((p (m.add 6)).mul (p (m.add 7)))).mul ((p (m.add 8)).mul
        ((p (m.add 9)).mul (p (m.add 10))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 5) =
      ((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * (q (m + 3) * q (m + 4))) + p m * p (m +
          1) * (p (m + 2) * (q (m + 3) * q (m + 4)) + p (m + 2) * (p (m + 3) * q (m + 4) + p (m +
          3) * p (m + 4))), q m * q (m + 1) * (q (m + 2) * (q (m + 3) * q (m + 4))), p m * p (m +
          1) * (p (m + 2) * (p (m + 3) * p (m + 4)))) :=
    binarySplit_of_base5 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 5) (m + 11) =
      ((p (m + 5) * (q (m + 6) * q (m + 7)) + p (m + 5) * (p (m + 6) * q (m + 7) + p (m + 6) * p
          (m + 7))) * (q (m + 8) * (q (m + 9) * q (m + 10))) + p (m + 5) * (p (m + 6) * p (m + 7))
          * (p (m + 8) * (q (m + 9) * q (m + 10)) + p (m + 8) * (p (m + 9) * q (m + 10) + p (m +
          9) * p (m + 10))), q (m + 5) * (q (m + 6) * q (m + 7)) * (q (m + 8) * (q (m + 9) * q (m
          + 10))), p (m + 5) * (p (m + 6) * p (m + 7)) * (p (m + 8) * (p (m + 9) * p (m + 10))))
          :=
    binarySplit_of_base6 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base12 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 12).beq n)
    (hT : T.beq (((((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul ((q (m.add 3)).mul ((q
        (m.add 4)).mul (q (m.add 5))))).add (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul
        (((p (m.add 3)).mul ((q (m.add 4)).mul (q (m.add 5)))).add ((p (m.add 3)).mul (((p (m.add
        4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add 5)))))))).mul (((q (m.add 6)).mul
        ((q (m.add 7)).mul (q (m.add 8)))).mul ((q (m.add 9)).mul ((q (m.add 10)).mul (q (m.add
        11)))))).add ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p (m.add 3)).mul ((p
        (m.add 4)).mul (p (m.add 5))))).mul (((((p (m.add 6)).mul ((q (m.add 7)).mul (q (m.add
        8)))).add ((p (m.add 6)).mul (((p (m.add 7)).mul (q (m.add 8))).add ((p (m.add 7)).mul (p
        (m.add 8)))))).mul ((q (m.add 9)).mul ((q (m.add 10)).mul (q (m.add 11))))).add (((p
        (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8)))).mul (((p (m.add 9)).mul ((q (m.add
        10)).mul (q (m.add 11)))).add ((p (m.add 9)).mul (((p (m.add 10)).mul (q (m.add 11))).add
        ((p (m.add 10)).mul (p (m.add 11)))))))))))
    (hQ : Q.beq ((((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul ((q (m.add 3)).mul ((q (m.add
        4)).mul (q (m.add 5))))).mul (((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add 8)))).mul
        ((q (m.add 9)).mul ((q (m.add 10)).mul (q (m.add 11)))))))
    (hP : P.beq ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p (m.add 3)).mul ((p (m.add
        4)).mul (p (m.add 5))))).mul (((p (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8)))).mul
        ((p (m.add 9)).mul ((p (m.add 10)).mul (p (m.add 11))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 6) =
      ((p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2))) *
          (q (m + 3) * (q (m + 4) * q (m + 5))) + p m * (p (m + 1) * p (m + 2)) * (p (m + 3) * (q
          (m + 4) * q (m + 5)) + p (m + 3) * (p (m + 4) * q (m + 5) + p (m + 4) * p (m + 5))), q m
          * (q (m + 1) * q (m + 2)) * (q (m + 3) * (q (m + 4) * q (m + 5))), p m * (p (m + 1) * p
          (m + 2)) * (p (m + 3) * (p (m + 4) * p (m + 5)))) :=
    binarySplit_of_base6 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 6) (m + 12) =
      ((p (m + 6) * (q (m + 7) * q (m + 8)) + p (m + 6) * (p (m + 7) * q (m + 8) + p (m + 7) * p
          (m + 8))) * (q (m + 9) * (q (m + 10) * q (m + 11))) + p (m + 6) * (p (m + 7) * p (m +
          8)) * (p (m + 9) * (q (m + 10) * q (m + 11)) + p (m + 9) * (p (m + 10) * q (m + 11) + p
          (m + 10) * p (m + 11))), q (m + 6) * (q (m + 7) * q (m + 8)) * (q (m + 9) * (q (m + 10)
          * q (m + 11))), p (m + 6) * (p (m + 7) * p (m + 8)) * (p (m + 9) * (p (m + 10) * p (m +
          11)))) :=
    binarySplit_of_base6 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base13 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 13).beq n)
    (hT : T.beq (((((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul ((q (m.add 3)).mul ((q
        (m.add 4)).mul (q (m.add 5))))).add (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul
        (((p (m.add 3)).mul ((q (m.add 4)).mul (q (m.add 5)))).add ((p (m.add 3)).mul (((p (m.add
        4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add 5)))))))).mul (((q (m.add 6)).mul
        ((q (m.add 7)).mul (q (m.add 8)))).mul (((q (m.add 9)).mul (q (m.add 10))).mul ((q (m.add
        11)).mul (q (m.add 12)))))).add ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p
        (m.add 3)).mul ((p (m.add 4)).mul (p (m.add 5))))).mul (((((p (m.add 6)).mul ((q (m.add
        7)).mul (q (m.add 8)))).add ((p (m.add 6)).mul (((p (m.add 7)).mul (q (m.add 8))).add ((p
        (m.add 7)).mul (p (m.add 8)))))).mul (((q (m.add 9)).mul (q (m.add 10))).mul ((q (m.add
        11)).mul (q (m.add 12))))).add (((p (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8)))).mul
        (((((p (m.add 9)).mul (q (m.add 10))).add ((p (m.add 9)).mul (p (m.add 10)))).mul ((q
        (m.add 11)).mul (q (m.add 12)))).add (((p (m.add 9)).mul (p (m.add 10))).mul (((p (m.add
        11)).mul (q (m.add 12))).add ((p (m.add 11)).mul (p (m.add 12)))))))))))
    (hQ : Q.beq ((((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul ((q (m.add 3)).mul ((q (m.add
        4)).mul (q (m.add 5))))).mul (((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add 8)))).mul
        (((q (m.add 9)).mul (q (m.add 10))).mul ((q (m.add 11)).mul (q (m.add 12)))))))
    (hP : P.beq ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p (m.add 3)).mul ((p (m.add
        4)).mul (p (m.add 5))))).mul (((p (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8)))).mul
        (((p (m.add 9)).mul (p (m.add 10))).mul ((p (m.add 11)).mul (p (m.add 12))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 6) =
      ((p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2))) *
          (q (m + 3) * (q (m + 4) * q (m + 5))) + p m * (p (m + 1) * p (m + 2)) * (p (m + 3) * (q
          (m + 4) * q (m + 5)) + p (m + 3) * (p (m + 4) * q (m + 5) + p (m + 4) * p (m + 5))), q m
          * (q (m + 1) * q (m + 2)) * (q (m + 3) * (q (m + 4) * q (m + 5))), p m * (p (m + 1) * p
          (m + 2)) * (p (m + 3) * (p (m + 4) * p (m + 5)))) :=
    binarySplit_of_base6 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 6) (m + 13) =
      ((p (m + 6) * (q (m + 7) * q (m + 8)) + p (m + 6) * (p (m + 7) * q (m + 8) + p (m + 7) * p
          (m + 8))) * (q (m + 9) * q (m + 10) * (q (m + 11) * q (m + 12))) + p (m + 6) * (p (m +
          7) * p (m + 8)) * ((p (m + 9) * q (m + 10) + p (m + 9) * p (m + 10)) * (q (m + 11) * q
          (m + 12)) + p (m + 9) * p (m + 10) * (p (m + 11) * q (m + 12) + p (m + 11) * p (m +
          12))), q (m + 6) * (q (m + 7) * q (m + 8)) * (q (m + 9) * q (m + 10) * (q (m + 11) * q
          (m + 12))), p (m + 6) * (p (m + 7) * p (m + 8)) * (p (m + 9) * p (m + 10) * (p (m + 11)
          * p (m + 12)))) :=
    binarySplit_of_base7 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base14 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 14).beq n)
    (hT : T.beq (((((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul (((q (m.add 3)).mul (q
        (m.add 4))).mul ((q (m.add 5)).mul (q (m.add 6))))).add (((p m).mul ((p (m.succ)).mul (p
        (m.add 2)))).mul (((((p (m.add 3)).mul (q (m.add 4))).add ((p (m.add 3)).mul (p (m.add
        4)))).mul ((q (m.add 5)).mul (q (m.add 6)))).add (((p (m.add 3)).mul (p (m.add 4))).mul
        (((p (m.add 5)).mul (q (m.add 6))).add ((p (m.add 5)).mul (p (m.add 6)))))))).mul (((q
        (m.add 7)).mul ((q (m.add 8)).mul (q (m.add 9)))).mul (((q (m.add 10)).mul (q (m.add
        11))).mul ((q (m.add 12)).mul (q (m.add 13)))))).add ((((p m).mul ((p (m.succ)).mul (p
        (m.add 2)))).mul (((p (m.add 3)).mul (p (m.add 4))).mul ((p (m.add 5)).mul (p (m.add
        6))))).mul (((((p (m.add 7)).mul ((q (m.add 8)).mul (q (m.add 9)))).add ((p (m.add 7)).mul
        (((p (m.add 8)).mul (q (m.add 9))).add ((p (m.add 8)).mul (p (m.add 9)))))).mul (((q
        (m.add 10)).mul (q (m.add 11))).mul ((q (m.add 12)).mul (q (m.add 13))))).add (((p (m.add
        7)).mul ((p (m.add 8)).mul (p (m.add 9)))).mul (((((p (m.add 10)).mul (q (m.add 11))).add
        ((p (m.add 10)).mul (p (m.add 11)))).mul ((q (m.add 12)).mul (q (m.add 13)))).add (((p
        (m.add 10)).mul (p (m.add 11))).mul (((p (m.add 12)).mul (q (m.add 13))).add ((p (m.add
        12)).mul (p (m.add 13)))))))))))
    (hQ : Q.beq ((((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul (((q (m.add 3)).mul (q (m.add
        4))).mul ((q (m.add 5)).mul (q (m.add 6))))).mul (((q (m.add 7)).mul ((q (m.add 8)).mul (q
        (m.add 9)))).mul (((q (m.add 10)).mul (q (m.add 11))).mul ((q (m.add 12)).mul (q (m.add
        13)))))))
    (hP : P.beq ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul (((p (m.add 3)).mul (p (m.add
        4))).mul ((p (m.add 5)).mul (p (m.add 6))))).mul (((p (m.add 7)).mul ((p (m.add 8)).mul (p
        (m.add 9)))).mul (((p (m.add 10)).mul (p (m.add 11))).mul ((p (m.add 12)).mul (p (m.add
        13))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 7) =
      ((p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2))) *
          (q (m + 3) * q (m + 4) * (q (m + 5) * q (m + 6))) + p m * (p (m + 1) * p (m + 2)) * ((p
          (m + 3) * q (m + 4) + p (m + 3) * p (m + 4)) * (q (m + 5) * q (m + 6)) + p (m + 3) * p
          (m + 4) * (p (m + 5) * q (m + 6) + p (m + 5) * p (m + 6))), q m * (q (m + 1) * q (m +
          2)) * (q (m + 3) * q (m + 4) * (q (m + 5) * q (m + 6))), p m * (p (m + 1) * p (m + 2)) *
          (p (m + 3) * p (m + 4) * (p (m + 5) * p (m + 6)))) :=
    binarySplit_of_base7 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 7) (m + 14) =
      ((p (m + 7) * (q (m + 8) * q (m + 9)) + p (m + 7) * (p (m + 8) * q (m + 9) + p (m + 8) * p
          (m + 9))) * (q (m + 10) * q (m + 11) * (q (m + 12) * q (m + 13))) + p (m + 7) * (p (m +
          8) * p (m + 9)) * ((p (m + 10) * q (m + 11) + p (m + 10) * p (m + 11)) * (q (m + 12) * q
          (m + 13)) + p (m + 10) * p (m + 11) * (p (m + 12) * q (m + 13) + p (m + 12) * p (m +
          13))), q (m + 7) * (q (m + 8) * q (m + 9)) * (q (m + 10) * q (m + 11) * (q (m + 12) * q
          (m + 13))), p (m + 7) * (p (m + 8) * p (m + 9)) * (p (m + 10) * p (m + 11) * (p (m + 12)
          * p (m + 13)))) :=
    binarySplit_of_base7 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base15 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 15).beq n)
    (hT : T.beq (((((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul (((q (m.add 3)).mul (q
        (m.add 4))).mul ((q (m.add 5)).mul (q (m.add 6))))).add (((p m).mul ((p (m.succ)).mul (p
        (m.add 2)))).mul (((((p (m.add 3)).mul (q (m.add 4))).add ((p (m.add 3)).mul (p (m.add
        4)))).mul ((q (m.add 5)).mul (q (m.add 6)))).add (((p (m.add 3)).mul (p (m.add 4))).mul
        (((p (m.add 5)).mul (q (m.add 6))).add ((p (m.add 5)).mul (p (m.add 6)))))))).mul ((((q
        (m.add 7)).mul (q (m.add 8))).mul ((q (m.add 9)).mul (q (m.add 10)))).mul (((q (m.add
        11)).mul (q (m.add 12))).mul ((q (m.add 13)).mul (q (m.add 14)))))).add ((((p m).mul ((p
        (m.succ)).mul (p (m.add 2)))).mul (((p (m.add 3)).mul (p (m.add 4))).mul ((p (m.add
        5)).mul (p (m.add 6))))).mul (((((((p (m.add 7)).mul (q (m.add 8))).add ((p (m.add 7)).mul
        (p (m.add 8)))).mul ((q (m.add 9)).mul (q (m.add 10)))).add (((p (m.add 7)).mul (p (m.add
        8))).mul (((p (m.add 9)).mul (q (m.add 10))).add ((p (m.add 9)).mul (p (m.add 10)))))).mul
        (((q (m.add 11)).mul (q (m.add 12))).mul ((q (m.add 13)).mul (q (m.add 14))))).add ((((p
        (m.add 7)).mul (p (m.add 8))).mul ((p (m.add 9)).mul (p (m.add 10)))).mul (((((p (m.add
        11)).mul (q (m.add 12))).add ((p (m.add 11)).mul (p (m.add 12)))).mul ((q (m.add 13)).mul
        (q (m.add 14)))).add (((p (m.add 11)).mul (p (m.add 12))).mul (((p (m.add 13)).mul (q
        (m.add 14))).add ((p (m.add 13)).mul (p (m.add 14)))))))))))
    (hQ : Q.beq ((((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul (((q (m.add 3)).mul (q (m.add
        4))).mul ((q (m.add 5)).mul (q (m.add 6))))).mul ((((q (m.add 7)).mul (q (m.add 8))).mul
        ((q (m.add 9)).mul (q (m.add 10)))).mul (((q (m.add 11)).mul (q (m.add 12))).mul ((q
        (m.add 13)).mul (q (m.add 14)))))))
    (hP : P.beq ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul (((p (m.add 3)).mul (p (m.add
        4))).mul ((p (m.add 5)).mul (p (m.add 6))))).mul ((((p (m.add 7)).mul (p (m.add 8))).mul
        ((p (m.add 9)).mul (p (m.add 10)))).mul (((p (m.add 11)).mul (p (m.add 12))).mul ((p
        (m.add 13)).mul (p (m.add 14))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 7) =
      ((p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2))) *
          (q (m + 3) * q (m + 4) * (q (m + 5) * q (m + 6))) + p m * (p (m + 1) * p (m + 2)) * ((p
          (m + 3) * q (m + 4) + p (m + 3) * p (m + 4)) * (q (m + 5) * q (m + 6)) + p (m + 3) * p
          (m + 4) * (p (m + 5) * q (m + 6) + p (m + 5) * p (m + 6))), q m * (q (m + 1) * q (m +
          2)) * (q (m + 3) * q (m + 4) * (q (m + 5) * q (m + 6))), p m * (p (m + 1) * p (m + 2)) *
          (p (m + 3) * p (m + 4) * (p (m + 5) * p (m + 6)))) :=
    binarySplit_of_base7 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 7) (m + 15) =
      (((p (m + 7) * q (m + 8) + p (m + 7) * p (m + 8)) * (q (m + 9) * q (m + 10)) + p (m + 7) * p
          (m + 8) * (p (m + 9) * q (m + 10) + p (m + 9) * p (m + 10))) * (q (m + 11) * q (m + 12)
          * (q (m + 13) * q (m + 14))) + p (m + 7) * p (m + 8) * (p (m + 9) * p (m + 10)) * ((p (m
          + 11) * q (m + 12) + p (m + 11) * p (m + 12)) * (q (m + 13) * q (m + 14)) + p (m + 11) *
          p (m + 12) * (p (m + 13) * q (m + 14) + p (m + 13) * p (m + 14))), q (m + 7) * q (m + 8)
          * (q (m + 9) * q (m + 10)) * (q (m + 11) * q (m + 12) * (q (m + 13) * q (m + 14))), p (m
          + 7) * p (m + 8) * (p (m + 9) * p (m + 10)) * (p (m + 11) * p (m + 12) * (p (m + 13) * p
          (m + 14)))) :=
    binarySplit_of_base8 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base16 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 16).beq n)
    (hT : T.beq (((((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul (q (m.add 3)))).add (((p m).mul (p (m.succ))).mul (((p (m.add 2)).mul (q (m.add
        3))).add ((p (m.add 2)).mul (p (m.add 3)))))).mul (((q (m.add 4)).mul (q (m.add 5))).mul
        ((q (m.add 6)).mul (q (m.add 7))))).add ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul
        (p (m.add 3)))).mul (((((p (m.add 4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add
        5)))).mul ((q (m.add 6)).mul (q (m.add 7)))).add (((p (m.add 4)).mul (p (m.add 5))).mul
        (((p (m.add 6)).mul (q (m.add 7))).add ((p (m.add 6)).mul (p (m.add 7)))))))).mul ((((q
        (m.add 8)).mul (q (m.add 9))).mul ((q (m.add 10)).mul (q (m.add 11)))).mul (((q (m.add
        12)).mul (q (m.add 13))).mul ((q (m.add 14)).mul (q (m.add 15)))))).add (((((p m).mul (p
        (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((p (m.add 4)).mul (p (m.add
        5))).mul ((p (m.add 6)).mul (p (m.add 7))))).mul (((((((p (m.add 8)).mul (q (m.add
        9))).add ((p (m.add 8)).mul (p (m.add 9)))).mul ((q (m.add 10)).mul (q (m.add 11)))).add
        (((p (m.add 8)).mul (p (m.add 9))).mul (((p (m.add 10)).mul (q (m.add 11))).add ((p (m.add
        10)).mul (p (m.add 11)))))).mul (((q (m.add 12)).mul (q (m.add 13))).mul ((q (m.add
        14)).mul (q (m.add 15))))).add ((((p (m.add 8)).mul (p (m.add 9))).mul ((p (m.add 10)).mul
        (p (m.add 11)))).mul (((((p (m.add 12)).mul (q (m.add 13))).add ((p (m.add 12)).mul (p
        (m.add 13)))).mul ((q (m.add 14)).mul (q (m.add 15)))).add (((p (m.add 12)).mul (p (m.add
        13))).mul (((p (m.add 14)).mul (q (m.add 15))).add ((p (m.add 14)).mul (p (m.add
        15)))))))))))
    (hQ : Q.beq (((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul (q (m.add 3)))).mul (((q
        (m.add 4)).mul (q (m.add 5))).mul ((q (m.add 6)).mul (q (m.add 7))))).mul ((((q (m.add
        8)).mul (q (m.add 9))).mul ((q (m.add 10)).mul (q (m.add 11)))).mul (((q (m.add 12)).mul
        (q (m.add 13))).mul ((q (m.add 14)).mul (q (m.add 15)))))))
    (hP : P.beq (((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((p
        (m.add 4)).mul (p (m.add 5))).mul ((p (m.add 6)).mul (p (m.add 7))))).mul ((((p (m.add
        8)).mul (p (m.add 9))).mul ((p (m.add 10)).mul (p (m.add 11)))).mul (((p (m.add 12)).mul
        (p (m.add 13))).mul ((p (m.add 14)).mul (p (m.add 15))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 8) =
      (((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * q (m + 3)) + p m * p (m + 1) * (p (m +
          2) * q (m + 3) + p (m + 2) * p (m + 3))) * (q (m + 4) * q (m + 5) * (q (m + 6) * q (m +
          7))) + p m * p (m + 1) * (p (m + 2) * p (m + 3)) * ((p (m + 4) * q (m + 5) + p (m + 4) *
          p (m + 5)) * (q (m + 6) * q (m + 7)) + p (m + 4) * p (m + 5) * (p (m + 6) * q (m + 7) +
          p (m + 6) * p (m + 7))), q m * q (m + 1) * (q (m + 2) * q (m + 3)) * (q (m + 4) * q (m +
          5) * (q (m + 6) * q (m + 7))), p m * p (m + 1) * (p (m + 2) * p (m + 3)) * (p (m + 4) *
          p (m + 5) * (p (m + 6) * p (m + 7)))) :=
    binarySplit_of_base8 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 8) (m + 16) =
      (((p (m + 8) * q (m + 9) + p (m + 8) * p (m + 9)) * (q (m + 10) * q (m + 11)) + p (m + 8) *
          p (m + 9) * (p (m + 10) * q (m + 11) + p (m + 10) * p (m + 11))) * (q (m + 12) * q (m +
          13) * (q (m + 14) * q (m + 15))) + p (m + 8) * p (m + 9) * (p (m + 10) * p (m + 11)) *
          ((p (m + 12) * q (m + 13) + p (m + 12) * p (m + 13)) * (q (m + 14) * q (m + 15)) + p (m
          + 12) * p (m + 13) * (p (m + 14) * q (m + 15) + p (m + 14) * p (m + 15))), q (m + 8) * q
          (m + 9) * (q (m + 10) * q (m + 11)) * (q (m + 12) * q (m + 13) * (q (m + 14) * q (m +
          15))), p (m + 8) * p (m + 9) * (p (m + 10) * p (m + 11)) * (p (m + 12) * p (m + 13) * (p
          (m + 14) * p (m + 15)))) :=
    binarySplit_of_base8 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
end BSN
end
end CertificatePort140


section CertificatePort141
section
namespace BSN
open Enclosure
open TangentNumbers
theorem bern_real_tangent_pos (m Tn p q : ℕ)
    (hT : tangentNumber (m + 1) = Tn)
    (hm : Nat.beq (m % 2) 0 = true)
    (hq : Nat.ble 1 q = true)
    (hcross : Nat.beq (p.mul ((Nat.pow 2 ((Nat.mul 2 m).add 2)).mul
          ((Nat.pow 2 ((Nat.mul 2 m).add 2)).sub 1)))
        (q.mul (((Nat.mul 2 m).add 2).mul Tn)) = true) :
    (bernoulli (2 * m + 2) : ℝ) = sfrac false p q := by
  have hme : Even m := Nat.even_iff.mpr (Nat.eq_of_beq_eq_true hm)
  have hq : 0 < q := pos_of_ble hq
  simp only [Nat.mul_eq, Nat.pow_eq, Nat.add_eq, Nat.sub_eq] at hcross
  have h1 : (1 : ℕ) ≤ 2 ^ (2 * m + 2) := Nat.one_le_two_pow
  have hcQ : ((p * (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1)) : ℕ) : ℚ)
      = ((q * ((2 * m + 2) * Tn) : ℕ) : ℚ) := by
    exact_mod_cast Nat.eq_of_beq_eq_true hcross
  push_cast [Nat.cast_sub h1] at hcQ
  have hQ : bernoulli (2 * m + 2) = (p : ℚ) / (q : ℚ) := by
    rw [bernoulli_eq_tangent_intDiv m, hT, hme.neg_one_pow, one_mul,
      div_eq_div_iff (by exact_mod_cast intDenom_ne_zero m)
        (by exact_mod_cast hq.ne')]
    push_cast [Nat.cast_sub h1]
    linear_combination -hcQ
  rw [hQ]
  exact sfrac_ratCast_natDiv p q
theorem bern_real_tangent_neg (m Tn p q : ℕ)
    (hT : tangentNumber (m + 1) = Tn)
    (hm : Nat.beq (m % 2) 1 = true)
    (hq : Nat.ble 1 q = true)
    (hcross : Nat.beq (p.mul ((Nat.pow 2 ((Nat.mul 2 m).add 2)).mul
          ((Nat.pow 2 ((Nat.mul 2 m).add 2)).sub 1)))
        (q.mul (((Nat.mul 2 m).add 2).mul Tn)) = true) :
    (bernoulli (2 * m + 2) : ℝ) = sfrac true p q := by
  have hmo : Odd m := Nat.odd_iff.mpr (Nat.eq_of_beq_eq_true hm)
  have hq : 0 < q := pos_of_ble hq
  simp only [Nat.mul_eq, Nat.pow_eq, Nat.add_eq, Nat.sub_eq] at hcross
  have h1 : (1 : ℕ) ≤ 2 ^ (2 * m + 2) := Nat.one_le_two_pow
  have hcQ : ((p * (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1)) : ℕ) : ℚ)
      = ((q * ((2 * m + 2) * Tn) : ℕ) : ℚ) := by
    exact_mod_cast Nat.eq_of_beq_eq_true hcross
  push_cast [Nat.cast_sub h1] at hcQ
  have hQ : bernoulli (2 * m + 2) = -((p : ℚ) / (q : ℚ)) := by
    rw [bernoulli_eq_tangent_intDiv m, hT, hmo.neg_one_pow, ← neg_div,
      div_eq_div_iff (by exact_mod_cast intDenom_ne_zero m)
        (by exact_mod_cast hq.ne')]
    push_cast [Nat.cast_sub h1]
    linear_combination hcQ
  rw [hQ, sfrac_true_div]
  push_cast
  ring
end BSN
end
end CertificatePort141
theorem BSN.bern_real_1 : @Eq Real
  (@Rat.cast Real Real.instRatCast
    (bernoulli
      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (Enclosure.sfrac Bool.false (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) :=
BSN.bern_real_tangent_pos (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 6) TangentNumbers.tangentNumberLit_1
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
theorem BSN.bern_real_2 : @Eq Real
  (@Rat.cast Real Real.instRatCast
    (bernoulli
      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (Enclosure.sfrac Bool.true (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) :=
BSN.bern_real_tangent_neg (nat_lit 1) (nat_lit 2) (nat_lit 1) (nat_lit 30) TangentNumbers.tangentNumberLit_2
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)


section CertificatePort142
section
namespace Enclosure
def numPos (neg : Bool) (cn : Nat) : Nat := if neg then 0 else cn
def numNeg (neg : Bool) (cn : Nat) : Nat := if neg then cn else 0
def recentreOk (cn cd rn rd cn' cd' rn' rd' : Nat) : Bool :=
  Nat.beq
    (Nat.add (Nat.sub (nat_lit 1) cd)
    (Nat.add (Nat.sub (nat_lit 1) cd')
    (Nat.add (Nat.sub (nat_lit 1) rd)
    (Nat.add (Nat.sub (nat_lit 1) rd')
    (Nat.add (Nat.sub (cn'.mul cd) (cn.mul cd'))
             (Nat.sub (((rn.mul (cd.mul cd')).add (((cn.mul cd').sub (cn'.mul cd)).mul rd)).mul rd')
                      (rn'.mul (rd.mul (cd.mul cd')))))))))
    (nat_lit 0)
end Enclosure
end
end CertificatePort142


section CertificatePort143
section
namespace Enclosure
def Real.IsNear (x : ℝ) (neg : Bool) (cn cd rn rd : ℕ) : Prop :=
  |x - sfrac neg cn cd| ≤ (rn : ℝ) / rd
theorem Real.IsNear.lower {x : ℝ} {neg : Bool} {cn cd rn rd : ℕ}
    (h : Real.IsNear x neg cn cd rn rd) : sfrac neg cn cd - (rn : ℝ) / rd ≤ x := by
  have := (abs_le.mp h).1; linarith
theorem Real.IsNear.upper {x : ℝ} {neg : Bool} {cn cd rn rd : ℕ}
    (h : Real.IsNear x neg cn cd rn rd) : x ≤ sfrac neg cn cd + (rn : ℝ) / rd := by
  have := (abs_le.mp h).2; linarith
theorem Real.IsNear.mk' {x : ℝ} {neg : Bool} {cn cd rn rd : ℕ}
    (hlo : sfrac neg cn cd - (rn : ℝ) / rd ≤ x) (hhi : x ≤ sfrac neg cn cd + (rn : ℝ) / rd) :
    Real.IsNear x neg cn cd rn rd := abs_le.mpr ⟨by linarith, by linarith⟩
theorem sfrac_eq_parts (neg : Bool) (cn cd : ℕ) :
    sfrac neg cn cd = ((numPos neg cn : ℝ) - (numNeg neg cn : ℝ)) / cd := by
  cases neg <;> simp [sfrac, numPos, numNeg, neg_div, sub_zero, zero_sub]
theorem abs_sfrac (neg : Bool) (cn cd : ℕ) : |sfrac neg cn cd| = (cn : ℝ) / cd := by
  rw [sfrac]
  cases neg <;> simp [abs_div, abs_of_nonneg]
theorem sfrac_mul (nx ny : Bool) (cnx cdx cny cdy : ℕ) :
    sfrac nx cnx cdx * sfrac ny cny cdy = sfrac (Bool.xor nx ny) (cnx * cny) (cdx * cdy) := by
  cases nx <;> cases ny <;> simp [sfrac] <;> ring
theorem Real.IsNear.const (neg : Bool) (cn cd : ℕ) :
    Real.IsNear (sfrac neg cn cd) neg cn cd (nat_lit 0) (nat_lit 1) := by
  simp [Real.IsNear]
theorem Real.IsNear.widen {x : ℝ} {n : Bool} {cn cd rn rd rn' rd' : ℕ}
    (h : Real.IsNear x n cn cd rn rd) (hrd : Nat.ble 1 rd) (hrd' : Nat.ble 1 rd')
    (hle : Nat.ble (rn.mul rd') (rn'.mul rd)) :
    Real.IsNear x n cn cd rn' rd' := by
  simp only [Nat.ble_eq, Nat.mul_eq] at hle
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hrd'R : (0:ℝ) < rd' := pos_real_of_ble hrd'
  simp only [Real.IsNear] at h ⊢
  refine le_trans h ?_
  rw [div_le_div_iff₀ hrdR hrd'R]
  exact_mod_cast hle
end Enclosure
end
end CertificatePort143


section CertificatePort144
section
namespace Enclosure
theorem Real.IsNear.add {x y : ℝ} {nx ny nR : Bool} {cnx cdx rnx rdx cny cdy rny rdy cnR : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy)
    (hrdx : Nat.ble (nat_lit 1) rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hnum : Nat.beq (((numPos nR cnR).add ((numNeg nx cnx).mul cdy)).add ((numNeg ny cny).mul cdx))
                    (((numNeg nR cnR).add ((numPos nx cnx).mul cdy)).add
                          ((numPos ny cny).mul cdx))) :
    Real.IsNear (x + y) nR cnR (cdx.mul cdy) ((rnx.mul rdy).add (rny.mul rdx)) (rdx.mul rdy) := by
  simp only [Nat.mul_eq, Nat.add_eq]
  have hcdxR : (0:ℝ) < cdx := pos_real_of_ble hcdx
  have hcdyR : (0:ℝ) < cdy := pos_real_of_ble hcdy
  have hrdxR : (0:ℝ) < rdx := pos_real_of_ble hrdx
  have hrdyR : (0:ℝ) < rdy := pos_real_of_ble hrdy
  have eR : (numPos nR cnR : ℝ) + (numNeg nx cnx : ℝ) * cdy + (numNeg ny cny : ℝ) * cdx
          = (numNeg nR cnR : ℝ) + (numPos nx cnx : ℝ) * cdy + (numPos ny cny : ℝ) * cdx := by
    have h' := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.add_eq, Nat.mul_eq] at h'
    exact_mod_cast h'
  have hc : sfrac nR cnR (cdx * cdy) = sfrac nx cnx cdx + sfrac ny cny cdy := by
    rw [sfrac_eq_parts nR cnR, sfrac_eq_parts nx cnx, sfrac_eq_parts ny cny,
      div_add_div _ _ (ne_of_gt hcdxR) (ne_of_gt hcdyR), Nat.cast_mul,
      div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (cdx : ℝ) * (cdy : ℝ) * eR
  have hrad : ((rnx * rdy + rny * rdx : ℕ) : ℝ) / ((rdx * rdy : ℕ) : ℝ)
            = (rnx : ℝ) / rdx + (rny : ℝ) / rdy := by
    rw [div_add_div _ _ (ne_of_gt hrdxR) (ne_of_gt hrdyR)]
    push_cast
    ring
  simp only [Real.IsNear] at hx hy ⊢
  rw [hc, hrad]
  calc |x + y - (sfrac nx cnx cdx + sfrac ny cny cdy)|
      = |(x - sfrac nx cnx cdx) + (y - sfrac ny cny cdy)| := by congr 1; ring
    _ ≤ |x - sfrac nx cnx cdx| + |y - sfrac ny cny cdy| := abs_add_le _ _
    _ ≤ (rnx : ℝ) / rdx + (rny : ℝ) / rdy := add_le_add hx hy
theorem Real.IsNear.neg {x : ℝ} {nx : Bool} {cnx cdx rnx rdx : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) : Real.IsNear (-x) (!nx) cnx cdx rnx rdx := by
  simp only [Real.IsNear, sfrac_not] at hx ⊢
  have : -x - -sfrac nx cnx cdx = -(x - sfrac nx cnx cdx) := by ring
  rwa [this, abs_neg]
theorem Real.IsNear.sub {x y : ℝ} {nx ny nR : Bool} {cnx cdx rnx rdx cny cdy rny rdy cnR : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy)
    (hrdx : Nat.ble (nat_lit 1) rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hnum : Nat.beq
        (((numPos nR cnR).add ((numNeg nx cnx).mul cdy)).add ((numNeg (!ny) cny).mul cdx))
        (((numNeg nR cnR).add ((numPos nx cnx).mul cdy)).add ((numPos (!ny) cny).mul cdx))) :
    Real.IsNear (x - y) nR cnR (cdx.mul cdy) ((rnx.mul rdy).add (rny.mul rdx)) (rdx.mul rdy) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg hcdx hcdy hrdx hrdy hnum
theorem abs_mul_sub {x y cx cy rx ry : ℝ} (hx : |x - cx| ≤ rx) (hy : |y - cy| ≤ ry) :
    |x * y - cx * cy| ≤ |cx| * ry + |cy| * rx + rx * ry := by
  have hrx : 0 ≤ rx := le_trans (abs_nonneg _) hx
  calc |x * y - cx * cy|
      = |cx * (y - cy) + cy * (x - cx) + (x - cx) * (y - cy)| := by congr 1; ring
    _ ≤ |cx * (y - cy) + cy * (x - cx)| + |(x - cx) * (y - cy)| := abs_add_le _ _
    _ ≤ (|cx * (y - cy)| + |cy * (x - cx)|) + |(x - cx) * (y - cy)| := by
        gcongr; exact abs_add_le _ _
    _ = |cx| * |y - cy| + |cy| * |x - cx| + |x - cx| * |y - cy| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |cx| * ry + |cy| * rx + rx * ry := by gcongr
theorem Real.IsNear.mul {x y : ℝ} {nx ny : Bool} {cnx cdx rnx rdx cny cdy rny rdy : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy)
    (hrdx : Nat.ble (nat_lit 1) rdx) (hrdy : Nat.ble (nat_lit 1) rdy) :
    Real.IsNear (x * y) (Bool.xor nx ny) (cnx.mul cny) (cdx.mul cdy)
      (((((cnx.mul rny).mul cdy).mul rdx).add (((cny.mul rnx).mul cdx).mul rdy)).add
        (((rnx.mul rny).mul cdx).mul cdy))
      (((cdx.mul cdy).mul rdx).mul rdy) := by
  simp only [Nat.mul_eq, Nat.add_eq]
  have hcdxR : (0:ℝ) < cdx := pos_real_of_ble hcdx
  have hcdyR : (0:ℝ) < cdy := pos_real_of_ble hcdy
  have hrdxR : (0:ℝ) < rdx := pos_real_of_ble hrdx
  have hrdyR : (0:ℝ) < rdy := pos_real_of_ble hrdy
  have hcdxN : 0 < cdx := pos_of_ble hcdx
  have hcdyN : 0 < cdy := pos_of_ble hcdy
  have hrdxN : 0 < rdx := pos_of_ble hrdx
  have hrdyN : 0 < rdy := pos_of_ble hrdy
  have hrad : (cnx : ℝ) / cdx * ((rny : ℝ) / rdy) + (cny : ℝ) / cdy * ((rnx : ℝ) / rdx)
              + (rnx : ℝ) / rdx * ((rny : ℝ) / rdy)
            = ((cnx * rny * cdy * rdx + cny * rnx * cdx * rdy + rnx * rny * cdx * cdy : ℕ) : ℝ)
              / ((cdx * cdy * rdx * rdy : ℕ) : ℝ) := by
    rw [eq_div_iff (by positivity)]
    push_cast
    field_simp
  simp only [Real.IsNear] at hx hy ⊢
  rw [← sfrac_mul]
  refine le_trans (abs_mul_sub hx hy) ?_
  rw [abs_sfrac, abs_sfrac, hrad]
private theorem ble_one_mul {a b : ℕ} (ha : Nat.ble (nat_lit 1) a
      = true) (hb : Nat.ble (nat_lit 1) b = true) :
    Nat.ble (nat_lit 1) (a.mul b) = true := by
  rw [Nat.ble_eq] at ha hb ⊢
  have h := Nat.mul_le_mul ha hb
  omega
theorem Real.IsNear.reprLit {x : ℝ} {n : Bool} {cn D Rn Rd cn' cd' rn' rd' : ℕ}
    (h : Real.IsNear x n cn D Rn Rd)
    (hD : Nat.ble (nat_lit 1) D) (hRd : Nat.ble (nat_lit 1) Rd) (hcd' : Nat.ble (nat_lit 1)
          cd') (hrd' : Nat.ble (nat_lit 1) rd')
    (hc : Nat.beq (cn.mul cd') (cn'.mul D))
    (hr : Nat.ble (Rn.mul rd') (rn'.mul Rd)) :
    Real.IsNear x n cn' cd' rn' rd' := by
  simp only [Nat.ble_eq, Nat.mul_eq] at hr
  have hDr : (0:ℝ) < D := pos_real_of_ble hD
  have hRdr : (0:ℝ) < Rd := pos_real_of_ble hRd
  have hcd'r : (0:ℝ) < cd' := pos_real_of_ble hcd'
  have hrd'r : (0:ℝ) < rd' := pos_real_of_ble hrd'
  have hceq : (cn : ℝ) / D = (cn' : ℝ) / cd' := by
    have hc' := Nat.eq_of_beq_eq_true hc
    simp only [Nat.mul_eq] at hc'
    rw [div_eq_div_iff hDr.ne' hcd'r.ne']; exact_mod_cast hc'
  have hsfrac : sfrac n cn D = sfrac n cn' cd' := by simp only [sfrac, hceq]
  have hrle : (Rn : ℝ) / Rd ≤ (rn' : ℝ) / rd' := by
    rw [div_le_div_iff₀ hRdr hrd'r]; exact_mod_cast hr
  simp only [Real.IsNear] at h ⊢
  rw [← hsfrac]
  exact le_trans h hrle
theorem Real.IsNear.addLit {x y : ℝ} {nx ny nR : Bool}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy) (hrdx : Nat.ble (nat_lit 1)
          rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hnum : Nat.beq (((numPos nR cnR).add ((numNeg nx cnx).mul cdy)).add ((numNeg ny cny).mul cdx))
                    (((numNeg nR cnR).add ((numPos nx cnx).mul cdy)).add ((numPos ny cny).mul cdx)))
    (hcdR' : Nat.ble (nat_lit 1) cdR') (hrdR' : Nat.ble (nat_lit 1) rdR')
    (hc : Nat.beq (cnR.mul cdR') (cnR'.mul (cdx.mul cdy)))
    (hr : Nat.ble (((rnx.mul rdy).add (rny.mul rdx)).mul rdR') (rnR'.mul (rdx.mul rdy))) :
    Real.IsNear (x + y) nR cnR' cdR' rnR' rdR' :=
  (hx.add hy hcdx hcdy hrdx hrdy hnum).reprLit
    (ble_one_mul hcdx hcdy) (ble_one_mul hrdx hrdy) hcdR' hrdR' hc hr
theorem Real.IsNear.subLit {x y : ℝ} {nx ny nR : Bool}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy) (hrdx : Nat.ble (nat_lit 1)
          rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hnum : Nat.beq
        (((numPos nR cnR).add ((numNeg nx cnx).mul cdy)).add ((numNeg (!ny) cny).mul cdx))
        (((numNeg nR cnR).add ((numPos nx cnx).mul cdy)).add ((numPos (!ny) cny).mul cdx)))
    (hcdR' : Nat.ble (nat_lit 1) cdR') (hrdR' : Nat.ble (nat_lit 1) rdR')
    (hc : Nat.beq (cnR.mul cdR') (cnR'.mul (cdx.mul cdy)))
    (hr : Nat.ble (((rnx.mul rdy).add (rny.mul rdx)).mul rdR') (rnR'.mul (rdx.mul rdy))) :
    Real.IsNear (x - y) nR cnR' cdR' rnR' rdR' :=
  (hx.sub hy hcdx hcdy hrdx hrdy hnum).reprLit
    (ble_one_mul hcdx hcdy) (ble_one_mul hrdx hrdy) hcdR' hrdR' hc hr
private theorem beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := by
  simpa [Nat.beq_eq_true_eq] using h
def addLitOk (cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' : ℕ) : Bool :=
  Nat.beq
    (Nat.add (Nat.sub (nat_lit 1) cdx)
    (Nat.add (Nat.sub (nat_lit 1) cdy)
    (Nat.add (Nat.sub (nat_lit 1) rdx)
    (Nat.add (Nat.sub (nat_lit 1) rdy)
    (Nat.add (Nat.sub (nat_lit 1) cdR')
    (Nat.add (Nat.sub (nat_lit 1) rdR')
    (Nat.add (Nat.sub (cnR.mul cdR') (cnR'.mul (cdx.mul cdy)))
    (Nat.add (Nat.sub (cnR'.mul (cdx.mul cdy)) (cnR.mul cdR'))
             (Nat.sub (((rnx.mul rdy).add (rny.mul rdx)).mul rdR')
                      (rnR'.mul (rdx.mul rdy)))))))))))
    (nat_lit 0)
private theorem addLitOk_parts {cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' : ℕ}
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Nat.ble (nat_lit 1) cdx = true ∧ Nat.ble (nat_lit 1) cdy = true ∧
    Nat.ble (nat_lit 1) rdx = true ∧ Nat.ble (nat_lit 1) rdy = true ∧
    Nat.ble (nat_lit 1) cdR' = true ∧ Nat.ble (nat_lit 1) rdR' = true ∧
    Nat.beq (cnR.mul cdR') (cnR'.mul (cdx.mul cdy)) = true ∧
    Nat.ble (((rnx.mul rdy).add (rny.mul rdx)).mul rdR') (rnR'.mul (rdx.mul rdy)) = true := by
  simp only [addLitOk, Nat.beq_eq, Nat.add_eq] at hs
  obtain ⟨z1, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z2, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z3, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z4, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z5, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z6, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z7, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z8, z9⟩ := Nat.add_eq_zero_iff.mp hs
  exact ⟨Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z1), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z2),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z3), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z4),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z5), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z6),
    beq_of_eq (Nat.le_antisymm (Nat.le_of_sub_eq_zero z7) (Nat.le_of_sub_eq_zero z8)),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z9)⟩
def mulLitOk (cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ) : Bool :=
  Nat.beq
    (Nat.add (Nat.sub (nat_lit 1) cdx)
    (Nat.add (Nat.sub (nat_lit 1) cdy)
    (Nat.add (Nat.sub (nat_lit 1) rdx)
    (Nat.add (Nat.sub (nat_lit 1) rdy)
    (Nat.add (Nat.sub (nat_lit 1) cdR)
    (Nat.add (Nat.sub (nat_lit 1) rdR)
    (Nat.add (Nat.sub ((cnx.mul cny).mul cdR) (cnR.mul (cdx.mul cdy)))
    (Nat.add (Nat.sub (cnR.mul (cdx.mul cdy)) ((cnx.mul cny).mul cdR))
             (Nat.sub ((((((cnx.mul rny).mul cdy).mul rdx).add
                         (((cny.mul rnx).mul cdx).mul rdy)).add
                         (((rnx.mul rny).mul cdx).mul cdy)).mul rdR)
                      (rnR.mul (((cdx.mul cdy).mul rdx).mul rdy)))))))))))
    (nat_lit 0)
private theorem mulLitOk_parts {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Nat.ble (nat_lit 1) cdx = true ∧ Nat.ble (nat_lit 1) cdy = true ∧
    Nat.ble (nat_lit 1) rdx = true ∧ Nat.ble (nat_lit 1) rdy = true ∧
    Nat.ble (nat_lit 1) cdR = true ∧ Nat.ble (nat_lit 1) rdR = true ∧
    Nat.beq ((cnx.mul cny).mul cdR) (cnR.mul (cdx.mul cdy)) = true ∧
    Nat.ble ((((((cnx.mul rny).mul cdy).mul rdx).add (((cny.mul rnx).mul cdx).mul rdy)).add
      (((rnx.mul rny).mul cdx).mul cdy)).mul rdR) (rnR.mul (((cdx.mul cdy).mul rdx).mul rdy))
      = true := by
  simp only [mulLitOk, Nat.beq_eq, Nat.add_eq] at hs
  obtain ⟨z1, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z2, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z3, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z4, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z5, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z6, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z7, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z8, z9⟩ := Nat.add_eq_zero_iff.mp hs
  exact ⟨Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z1), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z2),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z3), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z4),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z5), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z6),
    beq_of_eq (Nat.le_antisymm (Nat.le_of_sub_eq_zero z7) (Nat.le_of_sub_eq_zero z8)),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z9)⟩
theorem Real.IsNear.addLit_ff {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq cnR ((cnx.mul cdy).add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq, h])) hcdR' hrdR' hc hr
theorem Real.IsNear.addLit_tt {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq cnR ((cnx.mul cdy).add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq, h])) hcdR' hrdR' hc hr
theorem Real.IsNear.addLit_ft_p {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq (cnR.add (cny.mul cdx)) (cnx.mul cdy))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr
theorem Real.IsNear.addLit_ft_n {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq (cny.mul cdx) (cnR.add (cnx.mul cdy)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr
theorem Real.IsNear.addLit_tf_p {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq (cnR.add (cnx.mul cdy)) (cny.mul cdx))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr
theorem Real.IsNear.addLit_tf_n {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq (cnx.mul cdy) (cnR.add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr
theorem Real.IsNear.subLit_ff_p {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq (cnR.add (cny.mul cdx)) (cnx.mul cdy))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr
theorem Real.IsNear.subLit_ff_n {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq (cny.mul cdx) (cnR.add (cnx.mul cdy)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr
theorem Real.IsNear.subLit_ft {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq cnR ((cnx.mul cdy).add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq, h])) hcdR' hrdR' hc hr
theorem Real.IsNear.subLit_tf {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq cnR ((cnx.mul cdy).add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq, h])) hcdR' hrdR' hc hr
theorem Real.IsNear.subLit_tt_p {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq (cnR.add (cnx.mul cdy)) (cny.mul cdx))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr
theorem Real.IsNear.subLit_tt_n {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq (cnx.mul cdy) (cnR.add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr
theorem Real.IsNear.mulLit {x y : ℝ} {nx ny : Bool}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy) (hrdx : Nat.ble (nat_lit 1)
          rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hcdR : Nat.ble (nat_lit 1) cdR) (hrdR : Nat.ble (nat_lit 1) rdR)
    (hc : Nat.beq ((cnx.mul cny).mul cdR) (cnR.mul (cdx.mul cdy)))
    (hr : Nat.ble (((((((cnx.mul rny).mul cdy).mul rdx).add
        (((cny.mul rnx).mul cdx).mul rdy)).add (((rnx.mul rny).mul cdx).mul cdy)).mul rdR))
      (rnR.mul (((cdx.mul cdy).mul rdx).mul rdy))) :
    Real.IsNear (x * y) (Bool.xor nx ny) cnR cdR rnR rdR :=
  (hx.mul hy hcdx hcdy hrdx hrdy).reprLit (ble_one_mul hcdx hcdy)
    (ble_one_mul (ble_one_mul (ble_one_mul hcdx hcdy) hrdx) hrdy) hcdR hrdR hc hr
theorem Real.IsNear.mulLit_ff {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Real.IsNear (x * y) false cnR cdR rnR rdR :=
  by obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR, hrdR, hc, hr⟩ := mulLitOk_parts hs
     exact Real.IsNear.mulLit hx hy hcdx hcdy hrdx hrdy hcdR hrdR hc hr
theorem Real.IsNear.mulLit_ft {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Real.IsNear (x * y) true cnR cdR rnR rdR :=
  by obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR, hrdR, hc, hr⟩ := mulLitOk_parts hs
     exact Real.IsNear.mulLit hx hy hcdx hcdy hrdx hrdy hcdR hrdR hc hr
theorem Real.IsNear.mulLit_tf {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Real.IsNear (x * y) true cnR cdR rnR rdR :=
  by obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR, hrdR, hc, hr⟩ := mulLitOk_parts hs
     exact Real.IsNear.mulLit hx hy hcdx hcdy hrdx hrdy hcdR hrdR hc hr
theorem Real.IsNear.mulLit_tt {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Real.IsNear (x * y) false cnR cdR rnR rdR :=
  by obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR, hrdR, hc, hr⟩ := mulLitOk_parts hs
     exact Real.IsNear.mulLit hx hy hcdx hcdy hrdx hrdy hcdR hrdR hc hr
theorem Real.IsNear.recentre {x : ℝ} {n : Bool} {cn cd rn rd cn' cd' rn' rd' : ℕ}
    (h : Real.IsNear x n cn cd rn rd)
    (hcd : Nat.ble (nat_lit 1) cd) (hcd' : Nat.ble (nat_lit 1) cd') (hrd : Nat.ble (nat_lit 1)
          rd) (hrd' : Nat.ble (nat_lit 1) rd')
    (hfloor : Nat.ble (cn'.mul cd) (cn.mul cd'))
    (hrad : Nat.ble (((rn.mul (cd.mul cd')).add (((cn.mul cd').sub (cn'.mul cd)).mul rd)).mul rd')
                    (rn'.mul (rd.mul (cd.mul cd')))) :
    Real.IsNear x n cn' cd' rn' rd' := by
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hfloor hrad
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hcd'R : (0:ℝ) < cd' := pos_real_of_ble hcd'
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hrd'R : (0:ℝ) < rd' := pos_real_of_ble hrd'
  have hnn : (0:ℝ) ≤ (cn : ℝ) / cd - (cn' : ℝ) / cd' := by
    have : (cn' : ℝ) / cd' ≤ (cn : ℝ) / cd := by
      rw [div_le_div_iff₀ hcd'R hcdR]; exact_mod_cast hfloor
    linarith
  have hmagdiff : |sfrac n cn cd - sfrac n cn' cd'| = (cn : ℝ) / cd - (cn' : ℝ) / cd' := by
    have hsdiff : sfrac n cn cd - sfrac n cn' cd'
        = (if n then -1 else 1) * ((cn : ℝ) / cd - (cn' : ℝ) / cd') := by
      simp only [sfrac]; ring
    rw [hsdiff, abs_mul]; cases n <;> simp [abs_of_nonneg hnn]
  have hkey : (rn : ℝ) / rd + ((cn : ℝ) / cd - (cn' : ℝ) / cd') ≤ (rn' : ℝ) / rd' := by
    rw [div_sub_div _ _ (ne_of_gt hcdR) (ne_of_gt hcd'R),
      div_add_div _ _ (ne_of_gt hrdR) (by positivity), div_le_div_iff₀ (by positivity) hrd'R]
    have hcast : ((cn : ℝ) * cd' - cd * cn') = ((cn * cd' - cn' * cd : ℕ) : ℝ) := by
      rw [Nat.cast_sub hfloor]; push_cast; ring
    rw [hcast]
    have h2 : (((rn * (cd * cd') + (cn * cd' - cn' * cd) * rd) * rd' : ℕ) : ℝ)
            ≤ ((rn' * (rd * (cd * cd')) : ℕ) : ℝ) := by exact_mod_cast hrad
    push_cast at h2 ⊢
    nlinarith [h2]
  simp only [Real.IsNear] at h ⊢
  calc |x - sfrac n cn' cd'|
      ≤ |x - sfrac n cn cd| + |sfrac n cn cd - sfrac n cn' cd'| := abs_sub_le _ _ _
    _ ≤ (rn : ℝ) / rd + ((cn : ℝ) / cd - (cn' : ℝ) / cd') := by
      rw [hmagdiff]; exact add_le_add h le_rfl
    _ ≤ (rn' : ℝ) / rd' := hkey
theorem Real.IsNear.recentre' {x : ℝ} {n : Bool} {cn cd rn rd cn' cd' rn' rd' : ℕ}
    (h : Real.IsNear x n cn cd rn rd)
    (hs : recentreOk cn cd rn rd cn' cd' rn' rd' = true) :
    Real.IsNear x n cn' cd' rn' rd' := by
  simp only [recentreOk, Nat.beq_eq, Nat.add_eq] at hs
  obtain ⟨z1, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z2, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z3, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z4, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z5, z6⟩ := Nat.add_eq_zero_iff.mp hs
  exact Real.IsNear.recentre h
    (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z1)) (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z2))
    (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z3)) (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z4))
    (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z5)) (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z6))
end Enclosure
end
end CertificatePort144


section CertificatePort145
section
namespace Enclosure
theorem Real.IsNear.lipschitz_image {f : ℝ → ℝ} (hf : ∀ x y, |f x - f y| ≤ |x - y|)
    {x c : ℝ} {nc : Bool} {cn cd ρn ρd : ℕ}
    {sn : Bool} {scn scd rsn rsd : ℕ}
    (hx : Real.IsNear x nc cn cd ρn ρd)
    (hc : sfrac nc cn cd = c)
    (hsc : Real.IsNear (f c) sn scn scd rsn rsd)
    (hρd : Nat.ble 1 ρd) (hrsd : Nat.ble 1 rsd) :
    Real.IsNear (f x) sn scn scd ((rsn.mul ρd).add (ρn.mul rsd)) (rsd.mul ρd) := by
  subst hc
  simp only [Nat.mul_eq, Nat.add_eq]
  have hρdR : (0:ℝ) < ρd := pos_real_of_ble hρd
  have hrsdR : (0:ℝ) < rsd := pos_real_of_ble hrsd
  have hρdN : 0 < ρd := pos_of_ble hρd
  have hrsdN : 0 < rsd := pos_of_ble hrsd
  simp only [Real.IsNear] at hx hsc ⊢
  have hrad : ((rsn * ρd + ρn * rsd : ℕ) : ℝ) / ((rsd * ρd : ℕ) : ℝ)
            = (ρn : ℝ) / ρd + (rsn : ℝ) / rsd := by
    rw [div_eq_iff (by positivity)]; push_cast; field_simp; ring
  rw [hrad]
  calc |f x - sfrac sn scn scd|
      ≤ |f x - f (sfrac nc cn cd)| + |f (sfrac nc cn cd) - sfrac sn scn scd| :=
        abs_sub_le _ _ _
    _ ≤ |x - sfrac nc cn cd| + (rsn : ℝ) / rsd := add_le_add (hf _ _) hsc
    _ ≤ (ρn : ℝ) / ρd + (rsn : ℝ) / rsd := by linarith [hx]
theorem Real.IsNear.sin_image {x c : ℝ} {nc : Bool} {cn cd ρn ρd : ℕ}
    {sn : Bool} {scn scd rsn rsd : ℕ}
    (hx : Real.IsNear x nc cn cd ρn ρd)
    (hc : sfrac nc cn cd = c)
    (hsc : Real.IsNear (Real.sin c) sn scn scd rsn rsd)
    (hρd : Nat.ble 1 ρd) (hrsd : Nat.ble 1 rsd) :
    Real.IsNear (Real.sin x) sn scn scd ((rsn.mul ρd).add (ρn.mul rsd)) (rsd.mul ρd) :=
  lipschitz_image (fun _ _ => Real.abs_sin_sub_sin_le _ _) hx hc hsc hρd hrsd
theorem Real.IsNear.cos_image {x c : ℝ} {nc : Bool} {cn cd ρn ρd : ℕ}
    {sn : Bool} {scn scd rsn rsd : ℕ}
    (hx : Real.IsNear x nc cn cd ρn ρd)
    (hc : sfrac nc cn cd = c)
    (hsc : Real.IsNear (Real.cos c) sn scn scd rsn rsd)
    (hρd : Nat.ble 1 ρd) (hrsd : Nat.ble 1 rsd) :
    Real.IsNear (Real.cos x) sn scn scd ((rsn.mul ρd).add (ρn.mul rsd)) (rsd.mul ρd) :=
  lipschitz_image (fun _ _ => Real.abs_cos_sub_cos_le _ _) hx hc hsc hρd hrsd
theorem Real.IsNear.of_endpoints {z : ℝ} {a b Q : ℕ} (hQ : Nat.ble 1 Q)
    (h1 : (a : ℝ) / Q ≤ z) (h2 : z ≤ (b : ℝ) / Q) :
    Real.IsNear z false (a.add b) (Nat.mul (nat_lit 2) Q) (b.sub a) (Nat.mul (nat_lit 2) Q) := by
  have hQR : (0:ℝ) < Q := pos_real_of_ble hQ
  have hab : a ≤ b := by
    have hh : (a : ℝ) / Q ≤ (b : ℝ) / Q := le_trans h1 h2
    rw [div_le_div_iff₀ hQR hQR] at hh
    exact_mod_cast le_of_mul_le_mul_right hh hQR
  have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := Nat.cast_sub hab
  simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
  have hc1 : ((a : ℝ) + b) / (2 * Q) - ((b : ℝ) - a) / (2 * Q) = (a : ℝ) / Q := by field_simp; ring
  have hc2 : ((a : ℝ) + b) / (2 * Q) + ((b : ℝ) - a) / (2 * Q) = (b : ℝ) / Q := by field_simp; ring
  rw [Real.IsNear, sfrac_false_div, abs_le]
  push_cast [hcast]
  exact ⟨by linarith [h1, hc1], by linarith [h2, hc2]⟩
theorem Real.IsNear.sqrt_image {S : ℝ} {cn cd rn rd a b Q : ℕ}
    (hS : Real.IsNear S false cn cd rn rd)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd) (hQ : Nat.ble 1 Q)
    (hge : Nat.ble (rn.mul cd) (cn.mul rd))
    (hlo : Nat.ble ((a.pow 2).mul (cd.mul rd)) (((cn.mul rd).sub (rn.mul cd)).mul (Q.pow 2)))
    (hhi : Nat.ble (((cn.mul rd).add (rn.mul cd)).mul (Q.pow 2)) ((b.pow 2).mul (cd.mul rd))) :
    Real.IsNear (Real.sqrt S) false (a.add b) (Nat.mul (nat_lit 2) Q) (b.sub a)
      (Nat.mul (nat_lit 2) Q) := by
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.sub_eq] at hge hlo hhi
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hQR : (0:ℝ) < Q := pos_real_of_ble hQ
  have hsub : ((cn * rd - rn * cd : ℕ) : ℝ) = (cn : ℝ) * rd - rn * cd := by
    rw [Nat.cast_sub hge]; push_cast; ring
  have hQ2 : (0:ℝ) < (Q : ℝ) ^ 2 := by positivity
  have hcr : (0:ℝ) < (cd : ℝ) * rd := by positivity
  have hlo' : ((a : ℝ) / Q) ^ 2 ≤ (cn : ℝ) / cd - (rn : ℝ) / rd := by
    rw [div_pow, div_sub_div _ _ (ne_of_gt hcdR) (ne_of_gt hrdR), div_le_div_iff₀ hQ2 hcr]
    have h : ((a ^ 2 * (cd * rd) : ℕ) : ℝ) ≤ (((cn * rd - rn * cd) * Q ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hlo
    push_cast [hsub] at h; nlinarith [h]
  have hhi' : (cn : ℝ) / cd + (rn : ℝ) / rd ≤ ((b : ℝ) / Q) ^ 2 := by
    rw [div_pow, div_add_div _ _ (ne_of_gt hcdR) (ne_of_gt hrdR), div_le_div_iff₀ hcr hQ2]
    have h : (((cn * rd + rn * cd) * Q ^ 2 : ℕ) : ℝ) ≤ ((b ^ 2 * (cd * rd) : ℕ) : ℝ) := by
      exact_mod_cast hhi
    push_cast at h; nlinarith [h]
  have hSlo : (cn : ℝ) / cd - (rn : ℝ) / rd ≤ S := by have h := hS.lower; rwa [sfrac_false_div] at h
  have hShi : S ≤ (cn : ℝ) / cd + (rn : ℝ) / rd := by have h := hS.upper; rwa [sfrac_false_div] at h
  have h1 : (a : ℝ) / Q ≤ Real.sqrt S := by
    calc (a : ℝ) / Q = Real.sqrt (((a : ℝ) / Q) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((cn : ℝ) / cd - (rn : ℝ) / rd) := Real.sqrt_le_sqrt hlo'
      _ ≤ Real.sqrt S := Real.sqrt_le_sqrt hSlo
  have h2 : Real.sqrt S ≤ (b : ℝ) / Q := by
    calc Real.sqrt S ≤ Real.sqrt ((cn : ℝ) / cd + (rn : ℝ) / rd) := Real.sqrt_le_sqrt hShi
      _ ≤ Real.sqrt (((b : ℝ) / Q) ^ 2) := Real.sqrt_le_sqrt hhi'
      _ = (b : ℝ) / Q := Real.sqrt_sq (by positivity)
  exact Real.IsNear.of_endpoints hQ h1 h2
theorem Real.IsNear.of_interval {y y1 y2 : ℝ} {n1 n2 nR : Bool}
    {c1 d1 r1 e1 c2 d2 r2 e2 cnR cdR rnR rdR : ℕ}
    (h1 : Real.IsNear y1 n1 c1 d1 r1 e1) (h2 : Real.IsNear y2 n2 c2 d2 r2 e2)
    (hlo : y1 ≤ y) (hhi : y ≤ y2)
    (hd1 : Nat.ble 1 d1) (he1 : Nat.ble 1 e1) (hd2 : Nat.ble 1 d2) (he2 : Nat.ble 1 e2)
    (hcdR : Nat.ble 1 cdR) (hrdR : Nat.ble 1 rdR)
    (hL : Nat.ble ((((numPos nR cnR).mul ((rdR.mul d1).mul e1)).add
              ((numNeg n1 c1).mul ((cdR.mul rdR).mul e1))).add
              (r1.mul ((cdR.mul rdR).mul d1)))
            ((((numPos n1 c1).mul ((cdR.mul rdR).mul e1)).add
              ((numNeg nR cnR).mul ((rdR.mul d1).mul e1))).add
              (rnR.mul ((cdR.mul d1).mul e1))))
    (hH : Nat.ble ((((numPos n2 c2).mul ((cdR.mul rdR).mul e2)).add
              ((numNeg nR cnR).mul ((rdR.mul d2).mul e2))).add
              (r2.mul ((cdR.mul rdR).mul d2)))
            ((((numPos nR cnR).mul ((rdR.mul d2).mul e2)).add
              ((numNeg n2 c2).mul ((cdR.mul rdR).mul e2))).add
              (rnR.mul ((cdR.mul d2).mul e2)))) :
    Real.IsNear y nR cnR cdR rnR rdR := by
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at hL hH
  have hd1R : (0:ℝ) < d1 := pos_real_of_ble hd1
  have he1R : (0:ℝ) < e1 := pos_real_of_ble he1
  have hd2R : (0:ℝ) < d2 := pos_real_of_ble hd2
  have he2R : (0:ℝ) < e2 := pos_real_of_ble he2
  have hcdRR : (0:ℝ) < cdR := pos_real_of_ble hcdR
  have hrdRR : (0:ℝ) < rdR := pos_real_of_ble hrdR
  have hloR : sfrac nR cnR cdR - (rnR : ℝ) / rdR ≤ sfrac n1 c1 d1 - (r1 : ℝ) / e1 := by
    rw [sfrac_eq_parts nR cnR cdR, sfrac_eq_parts n1 c1 d1,
      div_sub_div _ _ hcdRR.ne' hrdRR.ne', div_sub_div _ _ hd1R.ne' he1R.ne',
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : ((numPos nR cnR * (rdR * d1 * e1) + numNeg n1 c1 * (cdR * rdR * e1)
                + r1 * (cdR * rdR * d1) : ℕ) : ℝ)
            ≤ ((numPos n1 c1 * (cdR * rdR * e1) + numNeg nR cnR * (rdR * d1 * e1)
                + rnR * (cdR * d1 * e1) : ℕ) : ℝ) := by exact_mod_cast hL
    push_cast at hc ⊢; nlinarith [hc]
  have hhiR : sfrac n2 c2 d2 + (r2 : ℝ) / e2 ≤ sfrac nR cnR cdR + (rnR : ℝ) / rdR := by
    rw [sfrac_eq_parts nR cnR cdR, sfrac_eq_parts n2 c2 d2,
      div_add_div _ _ hd2R.ne' he2R.ne', div_add_div _ _ hcdRR.ne' hrdRR.ne',
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : ((numPos n2 c2 * (cdR * rdR * e2) + numNeg nR cnR * (rdR * d2 * e2)
                + r2 * (cdR * rdR * d2) : ℕ) : ℝ)
            ≤ ((numPos nR cnR * (rdR * d2 * e2) + numNeg n2 c2 * (cdR * rdR * e2)
                + rnR * (cdR * d2 * e2) : ℕ) : ℝ) := by exact_mod_cast hH
    push_cast at hc ⊢; nlinarith [hc]
  exact Real.IsNear.mk' (le_trans hloR (le_trans h1.lower hlo))
    (le_trans hhi (le_trans h2.upper hhiR))
theorem Real.IsNear.inv_image {x : ℝ} {cn cd rn rd a b Q : ℕ}
    (hx : Real.IsNear x false cn cd rn rd)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd) (hQ : Nat.ble 1 Q)
    (hpos : Nat.blt (rn.mul cd) (cn.mul rd))
    (hlo : Nat.ble (a.mul ((cn.mul rd).add (rn.mul cd))) (Q.mul (cd.mul rd)))
    (hhi : Nat.ble (Q.mul (cd.mul rd)) (b.mul ((cn.mul rd).sub (rn.mul cd)))) :
    Real.IsNear x⁻¹ false (a.add b) (Nat.mul (nat_lit 2) Q) (b.sub a)
      (Nat.mul (nat_lit 2) Q) := by
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hpos hlo hhi
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hQR : (0:ℝ) < Q := pos_real_of_ble hQ
  have hposn : rn * cd < cn * rd := hpos
  have hsub : ((cn * rd - rn * cd : ℕ) : ℝ) = (cn : ℝ) * rd - rn * cd := by
    rw [Nat.cast_sub hposn.le]; push_cast; ring
  have hloQ : (0:ℝ) < (cn : ℝ) / cd - (rn : ℝ) / rd := by
    rw [div_sub_div _ _ hcdR.ne' hrdR.ne', lt_div_iff₀ (by positivity)]
    have h := hposn
    have : ((rn * cd : ℕ) : ℝ) < ((cn * rd : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; nlinarith [this]
  have hSlo : (cn : ℝ) / cd - (rn : ℝ) / rd ≤ x := by
    have h := hx.lower; rwa [sfrac_false_div] at h
  have hShi : x ≤ (cn : ℝ) / cd + (rn : ℝ) / rd := by
    have h := hx.upper; rwa [sfrac_false_div] at h
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le hloQ hSlo
  have hdiffR : (0:ℝ) < (cn : ℝ) * rd - (cd : ℝ) * rn := by
    have h' : ((rn * cd : ℕ) : ℝ) < ((cn * rd : ℕ) : ℝ) := by exact_mod_cast hposn
    push_cast at h'; linarith
  have hsumR : (0:ℝ) < (cn : ℝ) * rd + (cd : ℝ) * rn := by
    have hcdrn : (0:ℝ) ≤ (cd : ℝ) * rn := by positivity
    linarith
  have h1 : (a : ℝ) / Q ≤ x⁻¹ := by
    have hstep : (a : ℝ) / Q ≤ ((cn : ℝ) / cd + (rn : ℝ) / rd)⁻¹ := by
      rw [div_add_div _ _ hcdR.ne' hrdR.ne', inv_div, div_le_div_iff₀ hQR hsumR]
      have h' : ((a * (cn * rd + rn * cd) : ℕ) : ℝ) ≤ ((Q * (cd * rd) : ℕ) : ℝ) := by
        exact_mod_cast hlo
      push_cast at h'; nlinarith [h']
    exact le_trans hstep (inv_anti₀ hx0 hShi)
  have h2 : x⁻¹ ≤ (b : ℝ) / Q := by
    have hstep : ((cn : ℝ) / cd - (rn : ℝ) / rd)⁻¹ ≤ (b : ℝ) / Q := by
      rw [div_sub_div _ _ hcdR.ne' hrdR.ne', inv_div, div_le_div_iff₀ hdiffR hQR]
      have h' : ((Q * (cd * rd) : ℕ) : ℝ) ≤ ((b * (cn * rd - rn * cd) : ℕ) : ℝ) := by
        exact_mod_cast hhi
      push_cast [hsub] at h'; nlinarith [h']
    exact le_trans (inv_anti₀ hloQ hSlo) hstep
  exact Real.IsNear.of_endpoints hQ h1 h2
end Enclosure
end
end CertificatePort145


