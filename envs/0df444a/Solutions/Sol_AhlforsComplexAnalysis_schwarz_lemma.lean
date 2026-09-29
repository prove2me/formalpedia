-- Prove2me | solution 1 for AhlforsComplexAnalysis.schwarz_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T00:44:56.197587+00:00
-- url     : https://prove2.me/submissions/5af04933-2207-4e00-97bf-c79e809a281f

import Definitions.Def_AhlforsComplexAnalysis_Defs
import Mathlib

open AhlforsComplexAnalysis


namespace AhlforsComplexAnalysis

theorem schwarz_main {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    (hbound : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ 1) (h0 : f 0 = 0) :
    (∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ ‖z‖) ∧ ‖deriv f 0‖ ≤ 1 ∧
    (((∃ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 ∧ ‖f z‖ = ‖z‖) ∨ ‖deriv f 0‖ = 1) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, f z = c * z) := by
  have hd : DifferentiableOn ℂ f (Metric.ball 0 1) := hf.differentiableOn
  have hmaps : Set.MapsTo f (Metric.ball 0 1) (Metric.closedBall (f 0) 1) := by
    intro z hz
    rw [h0, Metric.mem_closedBall, dist_zero_right]
    exact hbound z hz
  refine ⟨fun z hz => ?_, ?_, ?_⟩
  · exact Complex.norm_le_norm_of_mapsTo_ball hd (by rwa [h0] at hmaps) h0
      (mem_ball_zero_iff.mp hz)
  · exact Complex.norm_deriv_le_one_of_mapsTo_ball hd hmaps one_pos
  · intro hcase
    obtain ⟨z₀, hz₀, heq⟩ : ∃ z₀ ∈ Metric.ball (0 : ℂ) 1, ‖dslope f 0 z₀‖ = 1 / 1 := by
      rcases hcase with ⟨z, hz, hz0, hfz⟩ | hder
      · refine ⟨z, hz, ?_⟩
        rw [dslope_of_ne _ hz0, slope_def_module, h0, sub_zero, sub_zero, norm_smul, norm_inv,
          hfz, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)]
        norm_num
      · refine ⟨0, Metric.mem_ball_self one_pos, ?_⟩
        rw [dslope_same, hder]; norm_num
    have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hd hmaps hz₀ heq
    refine ⟨dslope f 0 z₀, by rw [heq]; norm_num, fun z hz => ?_⟩
    rw [haff hz, h0]
    simp only [zero_add, sub_zero, smul_eq_mul, mul_comm]


theorem hurwitz_main {Ω : Set ℂ} (hΩ : IsRegion Ω) {F : ℕ → ℂ → ℂ}
    {f : ℂ → ℂ} (hF : ∀ n, AnalyticOnNhd ℂ (F n) Ω) (hF0 : ∀ n, ∀ z ∈ Ω, F n z ≠ 0)
    (hconv : ∀ K ⊆ Ω, IsCompact K → TendstoUniformlyOn F f Filter.atTop K) :
    (∀ z ∈ Ω, f z = 0) ∨ (∀ z ∈ Ω, f z ≠ 0) := by
  obtain ⟨hopen, hconn⟩ := hΩ
  have hFd : ∀ n, DifferentiableOn ℂ (F n) Ω := fun n => (hF n).differentiableOn
  have hloc : TendstoLocallyUniformlyOn F f Filter.atTop Ω :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).mpr hconv
  have hfd : DifferentiableOn ℂ f Ω :=
    hloc.differentiableOn (Filter.Eventually.of_forall hFd) hopen
  have hfa : AnalyticOnNhd ℂ f Ω := hfd.analyticOnNhd hopen
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨z1, hz1, hfz1⟩, ⟨z0, hz0, hfz0⟩⟩ := hcon
  -- the zero at z0 is isolated
  have hnotfreq : ¬ ∃ᶠ z in nhdsWithin z0 {z0}ᶜ, f z = 0 := by
    intro hfreq
    exact hfz1 (hfa.eqOn_zero_of_preconnected_of_frequently_eq_zero hconn.isPreconnected hz0
      hfreq hz1)
  rw [Filter.not_frequently] at hnotfreq
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hnotfreq
  obtain ⟨ε, hε, hεf⟩ := hnotfreq
  obtain ⟨ε', hε', hball⟩ := Metric.isOpen_iff.mp hopen z0 hz0
  set r := min ε ε' / 2 with hr
  have hrpos : 0 < r := by positivity
  have hr1 : r < ε := by have := min_le_left ε ε'; linarith
  have hr2 : r < ε' := by have := min_le_right ε ε'; linarith
  have hcb : Metric.closedBall z0 r ⊆ Ω :=
    (Metric.closedBall_subset_ball hr2).trans hball
  have hsph : ∀ z ∈ Metric.sphere z0 r, f z ≠ 0 := by
    intro z hz
    rw [Metric.mem_sphere] at hz
    refine hεf (by rw [hz]; exact hr1) ?_
    intro h; rw [h, dist_self] at hz; linarith
  -- minimum of |f| on the sphere
  have hsne : (Metric.sphere z0 r).Nonempty := ⟨z0 + r, by simp [abs_of_pos hrpos]⟩
  have hfc : ContinuousOn (fun z => ‖f z‖) (Metric.sphere z0 r) :=
    (hfd.continuousOn.mono (Metric.sphere_subset_closedBall.trans hcb)).norm
  obtain ⟨w, hw, hwmin⟩ := (isCompact_sphere z0 r).exists_isMinOn hsne hfc
  set m := ‖f w‖ with hm
  have hmpos : 0 < m := norm_pos_iff.mpr (hsph w hw)
  -- uniform approximation on the closed ball
  have hu := hconv _ hcb (isCompact_closedBall z0 r)
  rw [Metric.tendstoUniformlyOn_iff] at hu
  obtain ⟨n, hn⟩ := (hu (m / 2) (by positivity)).exists
  have hFsph : ∀ z ∈ Metric.sphere z0 r, m / 2 ≤ ‖F n z‖ := by
    intro z hz
    have h1 := hn z (Metric.sphere_subset_closedBall hz)
    have h2 : m ≤ ‖f z‖ := hwmin hz
    rw [dist_eq_norm] at h1
    have h3 := norm_sub_norm_le (f z) (F n z)
    linarith
  have hFz0 : ‖F n z0‖ < m / 2 := by
    have := hn z0 (Metric.mem_closedBall_self hrpos.le)
    rwa [dist_eq_norm, hfz0, zero_sub, norm_neg] at this
  -- maximum modulus for 1 / F n
  have hgd : DifferentiableOn ℂ (fun z => (F n z)⁻¹) Ω := (hFd n).inv (hF0 n)
  have hdc : DiffContOnCl ℂ (fun z => (F n z)⁻¹) (Metric.ball z0 r) :=
    hgd.diffContOnCl_ball hcb
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le (Metric.isBounded_ball) hdc
    (C := 2 / m) (fun z hz => by
      rw [frontier_ball z0 hrpos.ne'] at hz
      have := hFsph z hz
      have hne : F n z ≠ 0 := hF0 n z (hcb (Metric.sphere_subset_closedBall hz))
      rw [norm_inv]
      rw [inv_le_comm₀ (norm_pos_iff.mpr hne) (by positivity)]
      calc (2 / m)⁻¹ = m / 2 := by rw [inv_div]
        _ ≤ ‖F n z‖ := this)
    (subset_closure (Metric.mem_ball_self hrpos))
  have hne0 : F n z0 ≠ 0 := hF0 n z0 hz0
  rw [norm_inv, inv_le_comm₀ (norm_pos_iff.mpr hne0) (by positivity), inv_div] at hmax
  linarith

end AhlforsComplexAnalysis

open AhlforsComplexAnalysis

theorem solution {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    (hbound : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ 1) (h0 : f 0 = 0) :
    (∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ ‖z‖) ∧ ‖deriv f 0‖ ≤ 1 ∧
    (((∃ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 ∧ ‖f z‖ = ‖z‖) ∨ ‖deriv f 0‖ = 1) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, f z = c * z) := by
  exact schwarz_main hf hbound h0
