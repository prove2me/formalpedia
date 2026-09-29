-- Prove2me | solution 1 for AKR2008.dewitt_optimal_coupling
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T03:44:56.076674+00:00
-- url     : https://prove2.me/submissions/789e8607-5829-4d13-9079-56d6a85c12b2

import Mathlib
import Definitions.Def_AKR2008_Defs

open AKR2008
open scoped InnerProductSpace

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem W6_AKR2008_c_sq : (((1 / Real.sqrt 2 : ℝ) : ℂ)) * (((1 / Real.sqrt 2 : ℝ) : ℂ)) = 1 / 2 := by
  rw [← Complex.ofReal_mul]
  have : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
  rw [this]; push_cast; ring

theorem W6_AKR2008_inner_c {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ : H) (h : ‖Φ‖ = 1) :
    ⟪((1 / Real.sqrt 2 : ℝ) : ℂ) • Φ, ((1 / Real.sqrt 2 : ℝ) : ℂ) • Φ⟫_ℂ = 1 / 2 := by
  rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, h]
  rw [Complex.conj_ofReal, ← mul_assoc, W6_AKR2008_c_sq]; simp

theorem W6_AKR2008_inner_negc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ : H) (h : ‖Φ‖ = 1) :
    ⟪-(((1 / Real.sqrt 2 : ℝ) : ℂ) • Φ), -(((1 / Real.sqrt 2 : ℝ) : ℂ) • Φ)⟫_ℂ = 1 / 2 := by
  rw [inner_neg_left, inner_neg_right, neg_neg, W6_AKR2008_inner_c Φ h]

theorem W6_AKR2008_psiBefore_00 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) : psiBefore Φ₀ 0 0 = 0 := by simp [psiBefore, polKet]

theorem W6_AKR2008_psiBefore_11 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) : psiBefore Φ₀ 1 1 = 0 := by simp [psiBefore, polKet]

theorem W6_AKR2008_psiBefore_01 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) : psiBefore Φ₀ 0 1 = ((1 / Real.sqrt 2 : ℝ) : ℂ) • Φ₀ := by
  simp [psiBefore, polKet]

theorem W6_AKR2008_psiBefore_10 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) : psiBefore Φ₀ 1 0 = -(((1 / Real.sqrt 2 : ℝ) : ℂ) • Φ₀) := by
  simp [psiBefore, polKet]

theorem W6_AKR2008_psiAfter_00 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φup Φdown : H) : psiAfter Φup Φdown 0 0 = 0 := by simp [psiAfter, polKet]

theorem W6_AKR2008_psiAfter_11 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φup Φdown : H) : psiAfter Φup Φdown 1 1 = 0 := by simp [psiAfter, polKet]

theorem W6_AKR2008_psiAfter_01 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φup Φdown : H) : psiAfter Φup Φdown 0 1 = ((1 / Real.sqrt 2 : ℝ) : ℂ) • Φup := by
  simp [psiAfter, polKet]

theorem W6_AKR2008_psiAfter_10 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φup Φdown : H) : psiAfter Φup Φdown 1 0 = -(((1 / Real.sqrt 2 : ℝ) : ℂ) • Φdown) := by
  simp [psiAfter, polKet]

theorem W6_AKR2008_generic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Ψ : JointState H) (h00 : Ψ 0 0 = 0) (h11 : Ψ 1 1 = 0)
    (h01 : ⟪Ψ 0 1, Ψ 0 1⟫_ℂ = 1 / 2) (h10 : ⟪Ψ 1 0, Ψ 1 0⟫_ℂ = 1 / 2) :
    reducedPhoton2 Ψ = rhoHat := by
  have h01' : ((‖Ψ 0 1‖ : ℂ)) ^ 2 = 2⁻¹ := by
    simpa using h01
  have h10' : ((‖Ψ 1 0‖ : ℂ)) ^ 2 = 2⁻¹ := by
    simpa using h10
  ext j j'
  fin_cases j <;> fin_cases j' <;>
    simp [reducedPhoton2, rhoHat, Fin.sum_univ_two, polKet, Matrix.vecMulVec, h00, h11, h01, h10, h01', h10']

theorem W6_AKR2008_before_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) : reducedPhoton2 (psiBefore Φ₀) = rhoHat := by
  apply W6_AKR2008_generic
  · exact W6_AKR2008_psiBefore_00 Φ₀
  · exact W6_AKR2008_psiBefore_11 Φ₀
  · rw [W6_AKR2008_psiBefore_01]; exact W6_AKR2008_inner_c Φ₀ h₀
  · rw [W6_AKR2008_psiBefore_10]; exact W6_AKR2008_inner_negc Φ₀ h₀

theorem W6_AKR2008_after_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φup Φdown : H) (hup : ‖Φup‖ = 1) (hdown : ‖Φdown‖ = 1) :
    reducedPhoton2 (psiAfter Φup Φdown) = rhoHat := by
  apply W6_AKR2008_generic
  · exact W6_AKR2008_psiAfter_00 Φup Φdown
  · exact W6_AKR2008_psiAfter_11 Φup Φdown
  · rw [W6_AKR2008_psiAfter_01]; exact W6_AKR2008_inner_c Φup hup
  · rw [W6_AKR2008_psiAfter_10]; exact W6_AKR2008_inner_negc Φdown hdown

theorem W6_AKR2008_rhoHat_11 : rhoHat 1 1 = 1 / 2 := by
  simp [rhoHat, polKet, Matrix.vecMulVec]

theorem W6_AKR2008_rhoHat_00 : rhoHat 0 0 = 1 / 2 := by
  simp [rhoHat, polKet, Matrix.vecMulVec]

theorem W6_AKR2008_before_11 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) : reducedPhoton2 (psiBefore Φ₀) 1 1 = 1 / 2 := by
  rw [W6_AKR2008_before_eq Φ₀ h₀, W6_AKR2008_rhoHat_11]

-- targets

theorem W6_AKR2008_singlet_reduced_trace_11_eval
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 1 1 = 1 / 2 := W6_AKR2008_before_11 Φ₀ h₀

theorem W6_AKR2008_reducedPhoton2_psiBefore_11_eval_steps
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1)
    (h_zero : psiBefore Φ₀ 1 1 = 0)
    (h_comp : psiBefore Φ₀ 0 1 = ((1 / Real.sqrt 2 : ℝ) : ℂ) • Φ₀) :
    reducedPhoton2 (psiBefore Φ₀) 1 1 = 1 / 2 := W6_AKR2008_before_11 Φ₀ h₀

theorem W6_AKR2008_psiBefore_01_eq_smul
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) :
    psiBefore Φ₀ 0 1 = ((1 / Real.sqrt 2 : ℝ) : ℂ) • Φ₀ := W6_AKR2008_psiBefore_01 Φ₀

theorem W6_AKR2008_psiBefore_11_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) :
    psiBefore Φ₀ 1 1 = 0 := W6_AKR2008_psiBefore_11 Φ₀

theorem W6_AKR2008_reducedPhoton2_psiBefore_11_of_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1)
    (h : psiBefore Φ₀ 1 1 = 0) :
    reducedPhoton2 (psiBefore Φ₀) 1 1 = 1 / 2 := W6_AKR2008_before_11 Φ₀ h₀

theorem W6_AKR2008_rhoHat_11_val :
    rhoHat 1 1 = 1 / 2 := W6_AKR2008_rhoHat_11

theorem W6_AKR2008_rhoHat_00_val :
    rhoHat 0 0 = 1 / 2 := W6_AKR2008_rhoHat_00

theorem W6_AKR2008_photon2_same_reduced_state
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ Φup Φdown : H) (h₀ : ‖Φ₀‖ = 1) (hup : ‖Φup‖ = 1) (hdown : ‖Φdown‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) = rhoHat ∧ reducedPhoton2 (psiAfter Φup Φdown) = rhoHat :=
  ⟨W6_AKR2008_before_eq Φ₀ h₀, W6_AKR2008_after_eq Φup Φdown hup hdown⟩

theorem W6_AKR2008_reducedPhoton2_psiAfter
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φup Φdown : H) (hup : ‖Φup‖ = 1) (hdown : ‖Φdown‖ = 1) :
    reducedPhoton2 (psiAfter Φup Φdown) = rhoHat := W6_AKR2008_after_eq Φup Φdown hup hdown

theorem solution
    (ΔA ΔD : ℝ) (hA : 0 < ΔA) (hD : 0 < ΔD) :
    IsLeast ((fun g : ℝ => Real.sqrt (ΔA ^ 2 / g ^ 2 + g ^ 2 * ΔD ^ 2)) '' {g : ℝ | g ≠ 0})
      (Real.sqrt (2 * ΔA * ΔD)) := by
  constructor
  · refine ⟨Real.sqrt (ΔA / ΔD), ?_, ?_⟩
    · exact (Real.sqrt_pos.2 (div_pos hA hD)).ne'
    · simp only
      congr 1
      rw [Real.sq_sqrt (div_pos hA hD).le]
      field_simp
      ring
  · rintro y ⟨g, hg, rfl⟩
    have hg' : g ≠ 0 := hg
    apply Real.sqrt_le_sqrt
    have hg2 : 0 < g ^ 2 := by positivity
    have key : ΔA ^ 2 / g ^ 2 + g ^ 2 * ΔD ^ 2 - 2 * ΔA * ΔD = (ΔA / g - g * ΔD) ^ 2 := by
      field_simp
      ring
    nlinarith [sq_nonneg (ΔA / g - g * ΔD)]

theorem W6_AKR2008_singlet_reduced_trace_11_formula
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 1 1 = 1 / 2 := W6_AKR2008_before_11 Φ₀ h₀

theorem W6_AKR2008_reducedPhoton2_singlet_11_from_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 1 1 = 1 / 2 := W6_AKR2008_before_11 Φ₀ h₀

theorem W6_AKR2008_reducedPhoton2_singlet_unpolarized_11
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 1 1 = 1 / 2 := W6_AKR2008_before_11 Φ₀ h₀

theorem W6_AKR2008_singlet_partial_trace_11
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 1 1 = 1 / 2 := W6_AKR2008_before_11 Φ₀ h₀

theorem W6_AKR2008_reducedPhoton2_psiBefore_11_val
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 1 1 = 1 / 2 := W6_AKR2008_before_11 Φ₀ h₀
