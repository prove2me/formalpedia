-- Prove2me | solution 1 for Arxiv1303_0923.lemma5_modulus_determined_by_interval
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:30:29.51325+00:00
-- url     : https://prove2.me/submissions/78b8a170-2afb-4e74-9843-1707bc6ed5f9

import Mathlib
import Definitions.Def_Arxiv1303_0923_Basic

set_option autoImplicit false

open MeasureTheory Filter Topology
namespace Arxiv1303_0923

lemma l5_an (d : ℝ → ℂ) (hd : ∀ k : ℝ, AnalyticAt ℝ d k) (k : ℝ) :
    AnalyticAt ℝ (fun x => ‖d x‖ ^ 2) k := by
  have h1 : AnalyticAt ℝ (fun x => (d x).re) k :=
    (Complex.reCLM.analyticAt _).comp (hd k)
  have h2 : AnalyticAt ℝ (fun x => (d x).im) k :=
    (Complex.imCLM.analyticAt _).comp (hd k)
  have : (fun x => ‖d x‖ ^ 2) = fun x => (d x).re * (d x).re + (d x).im * (d x).im := by
    funext x; rw [Complex.sq_norm, Complex.normSq_apply]
  rw [this]
  exact (h1.mul h1).add (h2.mul h2)

theorem lemma5_modulus_determined_by_interval (a b : ℝ) (hab : a < b) (d1 d2 : ℝ → ℂ)
    (hd1 : ∀ k : ℝ, AnalyticAt ℝ d1 k) (hd2 : ∀ k : ℝ, AnalyticAt ℝ d2 k)
    (h : ∀ k ∈ Set.Ioo a b, ‖d1 k‖ = ‖d2 k‖) :
    ∀ k : ℝ, ‖d1 k‖ = ‖d2 k‖ := by
  set f : ℝ → ℝ := fun x => ‖d1 x‖ ^ 2 - ‖d2 x‖ ^ 2 with hf
  have han : AnalyticOnNhd ℝ f Set.univ := fun k _ => (l5_an d1 hd1 k).sub (l5_an d2 hd2 k)
  have hm : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  have hev : f =ᶠ[𝓝 ((a + b) / 2)] 0 := by
    filter_upwards [Ioo_mem_nhds hm.1 hm.2] with x hx
    simp [hf, h x hx]
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ _) hev
  intro k
  have hk : ‖d1 k‖ ^ 2 - ‖d2 k‖ ^ 2 = 0 := this (Set.mem_univ k)
  have h0 : ‖d1 k‖ ^ 2 = ‖d2 k‖ ^ 2 := by linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h0

end Arxiv1303_0923

open Arxiv1303_0923 in
theorem solution (a b : ℝ) (hab : a < b) (d1 d2 : ℝ → ℂ)
    (hd1 : ∀ k : ℝ, AnalyticAt ℝ d1 k) (hd2 : ∀ k : ℝ, AnalyticAt ℝ d2 k)
    (h : ∀ k ∈ Set.Ioo a b, ‖d1 k‖ = ‖d2 k‖) :
    ∀ k : ℝ, ‖d1 k‖ = ‖d2 k‖ := lemma5_modulus_determined_by_interval a b hab d1 d2 hd1 hd2 h
