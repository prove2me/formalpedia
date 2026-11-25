-- Prove2me | solution 1 for Arxiv1506_07229.inverse_permittivity_zero_on_imaginary_axis
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T14:51:36.881788+00:00
-- url     : https://prove2.me/submissions/43fdbb64-8e38-4e5d-868c-38589a4c3620

import Mathlib
import Definitions.Def_Arxiv1506_07229_Basic

open MeasureTheory Filter Topology Real ComplexConjugate

namespace Arxiv1506_07229

theorem inverse_permittivity_zero_on_imaginary_axis (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f upperHalf)
    (ha_real : ∀ u : ℝ, 0 ≤ u → (f ((u : ℂ) * Complex.I)).im = 0)
    (ha_cont : ContinuousOn (fun u : ℝ => f ((u : ℂ) * Complex.I)) (Set.Ici 0))
    (hb : (f 0).re < 0)
    (hc : Tendsto (fun u : ℝ => f ((u : ℂ) * Complex.I)) atTop (𝓝 1)) :
    ∃ u : ℝ, 0 < u ∧ f ((u : ℂ) * Complex.I) = 0 ∧
      Tendsto (fun z => ‖(f z)⁻¹‖) (𝓝[≠] ((u : ℂ) * Complex.I)) atTop := by
  have hopen : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  -- real part along the axis
  set g : ℝ → ℝ := fun u => (f ((u : ℂ) * Complex.I)).re with hg
  have gcont : ContinuousOn g (Set.Ici 0) := Complex.continuous_re.comp_continuousOn ha_cont
  have g0 : g 0 < 0 := by simp [hg, hb]
  have hcre : Tendsto g atTop (𝓝 1) := by
    have := (Complex.continuous_re.tendsto _).comp hc
    simpa [hg, Function.comp_def] using this
  obtain ⟨M, hM⟩ := (hcre.eventually (lt_mem_nhds (by norm_num : (1:ℝ)/2 < 1))).exists_forall_of_atTop
  set M' := max M 1
  have gM : 0 < g M' := by have := hM M' (le_max_left _ _); linarith
  have hivt : (0 : ℝ) ∈ Set.Icc (g 0) (g M') := ⟨g0.le, gM.le⟩
  obtain ⟨u, hu, hgu⟩ := intermediate_value_Icc (by positivity : (0:ℝ) ≤ M')
    (gcont.mono Set.Icc_subset_Ici_self) hivt
  have hu0 : 0 < u := by
    rcases hu.1.lt_or_eq with h | h
    · exact h
    · subst h; linarith
  have hfz : f ((u : ℂ) * Complex.I) = 0 := Complex.ext hgu (by simpa using ha_real u hu0.le)
  refine ⟨u, hu0, hfz, ?_⟩
  set z0 : ℂ := (u : ℂ) * Complex.I
  have hz0 : z0 ∈ upperHalf := by show 0 < z0.im; simp [z0, hu0]
  have hanal : AnalyticOnNhd ℂ f upperHalf := hf.analyticOnNhd hopen
  -- zeros are isolated
  have hne : ∀ᶠ z in 𝓝[≠] z0, f z ≠ 0 := by
    rcases (hanal z0 hz0).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have hconn : IsPreconnected upperHalf :=
        (convex_halfSpace_im_gt (0:ℝ)).isPreconnected
      have hzero := hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz0 h
      have hlim : Tendsto (fun u : ℝ => f ((u : ℂ) * Complex.I)) atTop (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop (0:ℝ)] with v hv
        exact (hzero (show 0 < ((v : ℂ) * Complex.I).im by simp [hv])).symm
      exact one_ne_zero (tendsto_nhds_unique hc hlim)
    · exact h
  have hcont : ContinuousAt f z0 := (hanal z0 hz0).continuousAt
  have h0 : Tendsto (fun z => ‖f z‖) (𝓝[≠] z0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto f (𝓝[≠] z0) (𝓝 0) := by
        rw [← hfz]; exact hcont.tendsto.mono_left nhdsWithin_le_nhds
      simpa using this.norm
    · filter_upwards [hne] with z hz
      exact norm_pos_iff.mpr hz
  have := tendsto_inv_nhdsGT_zero.comp h0
  refine this.congr' ?_
  filter_upwards with z
  simp [Function.comp_def, norm_inv]

end Arxiv1506_07229
open Arxiv1506_07229 in
theorem solution (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f upperHalf)
    (ha_real : ∀ u : ℝ, 0 ≤ u → (f ((u : ℂ) * Complex.I)).im = 0)
    (ha_cont : ContinuousOn (fun u : ℝ => f ((u : ℂ) * Complex.I)) (Set.Ici 0))
    (hb : (f 0).re < 0)
    (hc : Tendsto (fun u : ℝ => f ((u : ℂ) * Complex.I)) atTop (𝓝 1)) :
    ∃ u : ℝ, 0 < u ∧ f ((u : ℂ) * Complex.I) = 0 ∧
      Tendsto (fun z => ‖(f z)⁻¹‖) (𝓝[≠] ((u : ℂ) * Complex.I)) atTop :=
  inverse_permittivity_zero_on_imaginary_axis f hf ha_real ha_cont hb hc
