-- Prove2me | solution 2 for AhlforsComplexAnalysis.exists_log_and_root
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T12:37:22.999248+00:00
-- url     : https://prove2.me/submissions/5d154ab1-e7c8-4766-ac38-6e02b8e75b6c

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Defs
import Definitions.Def_AhlforsComplexAnalysis_Polygon
import Theorems.Thm_AhlforsComplexAnalysis_Polygon_cauchy_polygon
import Theorems.Thm_AhlforsComplexAnalysis_Polygon_windInt_eq_zero_of_connected_compl
import Theorems.Thm_AhlforsComplexAnalysis_Polygon_exists_primitive_of_polyInt_zero

set_option autoImplicit false

open AhlforsComplexAnalysis
open AhlforsComplexAnalysis.Polygon

theorem solution {Ω : Set ℂ}
    (hΩ : IsSimplyConnectedRegion Ω) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω) (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    (∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L Ω ∧ ∀ z ∈ Ω, Complex.exp (L z) = f z) ∧
    ∀ n : ℕ, 0 < n → ∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R Ω ∧ ∀ z ∈ Ω, R z ^ n = f z := by
  obtain ⟨⟨hΩo, hΩc⟩, hcompl⟩ := hΩ
  set g : ℂ → ℂ := fun z => deriv f z / f z with hg
  have hga : AnalyticOnNhd ℂ g Ω := hf.deriv.div hf hf0
  have hgc : ContinuousOn g Ω := hga.continuousOn
  have h0 : ∀ l : List ℂ, IsClosedPoly l → PolyIn Ω l → polyInt g l = 0 := by
    intro l hl hlΩ
    exact cauchy_polygon hΩo hga.differentiableOn hl hlΩ
      (fun a ha => windInt_eq_zero_of_connected_compl hΩo hcompl hl hlΩ ha)
  obtain ⟨G, hG⟩ := exists_primitive_of_polyInt_zero hΩo hΩc hgc h0
  have hGd : DifferentiableOn ℂ G Ω := fun z hz => (hG z hz).differentiableAt.differentiableWithinAt
  have hfd : ∀ z ∈ Ω, HasDerivAt f (deriv f z) z :=
    fun z hz => (hf z hz).differentiableAt.hasDerivAt
  have hh : ∀ z ∈ Ω, HasDerivAt (fun z => f z * Complex.exp (-G z)) 0 z := by
    intro z hz
    have h1 := (hfd z hz).mul (hG z hz).neg.cexp
    refine h1.congr_deriv ?_
    have h2 : g z = deriv f z / f z := rfl
    have := hf0 z hz
    rw [h2]
    field_simp
    try ring
  obtain ⟨c, hc⟩ := hΩo.exists_is_const_of_deriv_eq_zero hΩc.isPreconnected
    (f := fun z => f z * Complex.exp (-G z))
    (fun z hz => (hh z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hh z hz).deriv)
  obtain ⟨z₀, hz₀⟩ := hΩc.nonempty
  have hc0 : c ≠ 0 := by
    rw [← hc z₀ hz₀]
    exact mul_ne_zero (hf0 z₀ hz₀) (Complex.exp_ne_zero _)
  have hfc : ∀ z ∈ Ω, f z = c * Complex.exp (G z) := by
    intro z hz
    have := hc z hz
    calc f z = f z * Complex.exp (-G z) * Complex.exp (G z) := by
          rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = c * Complex.exp (G z) := by rw [this]
  have hLd : DifferentiableOn ℂ (fun z => G z + Complex.log c) Ω := hGd.add_const _
  have hLa : AnalyticOnNhd ℂ (fun z => G z + Complex.log c) Ω := hLd.analyticOnNhd hΩo
  have hLexp : ∀ z ∈ Ω, Complex.exp (G z + Complex.log c) = f z := by
    intro z hz
    rw [Complex.exp_add, Complex.exp_log hc0, hfc z hz, mul_comm]
  refine ⟨⟨fun z => G z + Complex.log c, hLa, hLexp⟩, ?_⟩
  intro n hn
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  refine ⟨fun z => Complex.exp ((G z + Complex.log c) / n), ?_, ?_⟩
  · exact ((hLd.div_const (n : ℂ)).cexp).analyticOnNhd hΩo
  · intro z hz
    rw [← Complex.exp_nat_mul]
    have : (n : ℂ) * ((G z + Complex.log c) / n) = G z + Complex.log c := by
      field_simp
    rw [this]
    exact hLexp z hz

#print axioms solution
