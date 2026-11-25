-- Prove2me | solution 1 for Arxiv2111_09089.cayley_map_properties
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T20:14:20.37193+00:00
-- url     : https://prove2.me/submissions/c7df4d6a-e00a-40c2-96e1-81a017235d74

import Mathlib
import Definitions.Def_Arxiv2111_09089_Basic

open Complex MeasureTheory Filter Topology Asymptotics
open Arxiv2111_09089

lemma cm_im (η : ℂ) (h1 : ‖η‖ = 1) (hne : η ≠ 1) : (cayley η).im = 0 := by
  have hn : η.re ^ 2 + η.im ^ 2 = 1 := by
    have := Complex.sq_norm η
    rw [h1, Complex.normSq_apply] at this
    nlinarith [this]
  simp only [cayley, Complex.div_im]
  simp
  rw [div_sub_div_same]
  apply div_eq_zero_iff.mpr
  left
  linear_combination hn

lemma cm_deriv (η : ℂ) (h : η ≠ 1) : HasDerivAt cayley (-2 * I / (1 - η) ^ 2) η := by
  have h1 : (1 : ℂ) - η ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hn := (((hasDerivAt_id η).const_add 1).const_mul (-I)).div
    ((hasDerivAt_id η).const_sub 1) h1
  have hf : cayley = fun x => -I * (1 + id x) / (1 - id x) := by
    funext x; simp [cayley]
  rw [hf]
  refine hn.congr_deriv ?_
  simp only [id]
  field_simp
  ring

lemma cm_zero : cayley 0 = -I := by simp [cayley]

lemma cm_inf : Tendsto cayley (cocompact ℂ) (𝓝 I) := by
  have hinv : Tendsto (fun η : ℂ => η⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]; exact tendsto_inv₀_cobounded
  have hF : Tendsto (fun w : ℂ => -I * (w + 1) / (w - 1)) (𝓝 0) (𝓝 I) := by
    have : ContinuousAt (fun w : ℂ => -I * (w + 1) / (w - 1)) 0 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      norm_num
    have h2 := this.tendsto
    convert h2 using 2
    simp
  have hev : ∀ᶠ η in cocompact ℂ, η ≠ 0 ∧ η ≠ 1 := by
    have a := (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
    have b := (isCompact_singleton (x := (1 : ℂ))).compl_mem_cocompact
    filter_upwards [a, b] with η ha hb
    exact ⟨ha, hb⟩
  refine (hF.comp hinv).congr' ?_
  filter_upwards [hev] with η ⟨h0, h1⟩
  have h1' : (1 : ℂ) - η ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h2' : η⁻¹ - 1 ≠ 0 := by
    intro h; apply h1; have := inv_eq_one.mp (sub_eq_zero.mp h); exact this
  simp only [Function.comp, cayley]
  field_simp

lemma cm_unique (μ : ℝ) : ∃! η : ℂ, ‖η‖ = 1 ∧ η ≠ 1 ∧ cayley η = (μ : ℂ) := by
  have hm : (μ : ℂ) - I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hp : (μ : ℂ) + I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  refine ⟨((μ : ℂ) + I) / ((μ : ℂ) - I), ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [norm_div]
    have : (μ : ℂ) - I = (starRingEnd ℂ) ((μ : ℂ) + I) := by simp [map_add, Complex.conj_ofReal]; ring
    rw [this, Complex.norm_conj, div_self]
    exact norm_ne_zero_iff.mpr hp
  · intro h
    rw [div_eq_one_iff_eq hm] at h
    have := congrArg Complex.im h; simp at this; norm_num at this
  · have hd : (1 : ℂ) - ((μ : ℂ) + I) / ((μ : ℂ) - I) ≠ 0 := by
      rw [one_sub_div hm]; apply div_ne_zero _ hm
      ring_nf; simp [Complex.I_ne_zero]
    simp only [cayley]
    rw [div_eq_iff hd]
    field_simp
    ring_nf
  · rintro η ⟨_, hne, hc⟩
    have h1 : (1 : ℂ) - η ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    simp only [cayley] at hc
    rw [div_eq_iff h1] at hc
    rw [eq_div_iff hm]
    linear_combination hc

theorem solution (α : ℝ) (_hα : 0 < α) :
    (∀ η : ℂ, ‖η‖ = 1 → η ≠ 1 → (cayley η).im = 0) ∧
    (∀ μ : ℝ, ∃! η : ℂ, ‖η‖ = 1 ∧ η ≠ 1 ∧ cayley η = (μ : ℂ)) ∧
    cayley 0 = -I ∧
    Tendsto cayley (cocompact ℂ) (𝓝 I) ∧
    (∀ η : ℂ, η ≠ 1 → HasDerivAt cayley (-2 * I / (1 - η) ^ 2) η) ∧
    ∀ g : ℂ → ℂ, ContinuousAt g (xiOfMu α (-I)) → ContinuousAt g (xiOfMu α I) →
      Tendsto (fun η => g (xiOfMu α (cayley η))) (𝓝 0) (𝓝 (g (xiOfMu α (-I)))) ∧
      Tendsto (fun η => g (xiOfMu α (cayley η))) (cocompact ℂ) (𝓝 (g (xiOfMu α I))) := by
  have hx : Continuous (xiOfMu α) := by unfold xiOfMu; fun_prop
  refine ⟨cm_im, cm_unique, cm_zero, cm_inf, cm_deriv, ?_⟩
  intro g hg1 hg2
  have hc0 : Tendsto cayley (𝓝 0) (𝓝 (-I)) := by
    have := (cm_deriv 0 (by norm_num)).continuousAt.tendsto
    rwa [cm_zero] at this
  exact ⟨hg1.tendsto.comp ((hx.tendsto _).comp hc0), hg2.tendsto.comp ((hx.tendsto _).comp cm_inf)⟩

