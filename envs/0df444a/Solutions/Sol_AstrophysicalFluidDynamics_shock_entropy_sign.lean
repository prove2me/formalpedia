-- Prove2me | solution 1 for AstrophysicalFluidDynamics.shock_entropy_sign
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:01:32.689911+00:00
-- url     : https://prove2.me/submissions/e1b12605-ca1d-474f-9b79-7e03ebba0f89

import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs
import Mathlib

open Filter Topology
open AstrophysicalFluidDynamics

namespace LU3EntropyHelpers

noncomputable def psi (γ y : ℝ) : ℝ :=
  Real.log (2 * γ * y - γ + 1) - γ * Real.log y + γ * Real.log ((γ - 1) * y + 2)

lemma psi_deriv (γ y : ℝ) (hγ : 1 < γ) (hy : 0 < y) (hA : 0 < 2 * γ * y - γ + 1) :
    HasDerivAt (psi γ) (2 * γ * (γ - 1) * (y - 1) ^ 2 /
      ((2 * γ * y - γ + 1) * y * ((γ - 1) * y + 2))) y := by
  have hB : 0 < (γ - 1) * y + 2 := by nlinarith
  have h1 : HasDerivAt (fun x => 2 * γ * x - γ + 1) (2 * γ * 1) y :=
    (((hasDerivAt_id' y).const_mul (2 * γ)).sub_const γ).add_const 1
  have h2 : HasDerivAt (fun x => (γ - 1) * x + 2) ((γ - 1) * 1) y :=
    ((hasDerivAt_id' y).const_mul (γ - 1)).add_const 2
  have h := ((h1.log hA.ne').sub ((Real.hasDerivAt_log hy.ne').const_mul γ)).add
    ((h2.log hB.ne').const_mul γ)
  have e : 2 * γ * 1 / (2 * γ * y - γ + 1) - γ * y⁻¹ + γ * ((γ - 1) * 1 / ((γ - 1) * y + 2))
      = 2 * γ * (γ - 1) * (y - 1) ^ 2 / ((2 * γ * y - γ + 1) * y * ((γ - 1) * y + 2)) := by
    have := hA.ne'
    have := hB.ne'
    have := hy.ne'
    rw [eq_div_iff (by positivity), div_eq_mul_inv, div_eq_mul_inv]
    have i1 : (2 * γ * y - γ + 1) * (2 * γ * y - γ + 1)⁻¹ = 1 := mul_inv_cancel₀ hA.ne'
    have i2 : ((γ - 1) * y + 2) * ((γ - 1) * y + 2)⁻¹ = 1 := mul_inv_cancel₀ hB.ne'
    have i3 : y * y⁻¹ = 1 := mul_inv_cancel₀ hy.ne'
    linear_combination (2 * γ * 1 * (y * ((γ - 1) * y + 2))) * i1
      - γ * ((2 * γ * y - γ + 1) * ((γ - 1) * y + 2)) * i3
      + γ * (γ - 1) * 1 * ((2 * γ * y - γ + 1) * y) * i2
  exact h.congr_deriv e

lemma psi_cont (γ : ℝ) (hγ : 1 < γ) (D : Set ℝ)
    (hD : ∀ y ∈ D, 0 < y ∧ 0 < 2 * γ * y - γ + 1) : ContinuousOn (psi γ) D :=
  fun y hy => (psi_deriv γ y hγ (hD y hy).1 (hD y hy).2).continuousAt.continuousWithinAt

lemma psi_one (γ : ℝ) : psi γ 1 = (1 + γ) * Real.log (γ + 1) := by
  unfold psi
  rw [Real.log_one]
  ring_nf

lemma psi_pos_deriv (γ y : ℝ) (hγ : 1 < γ) (hy : 0 < y) (hA : 0 < 2 * γ * y - γ + 1)
    (hy1 : y ≠ 1) : 0 < deriv (psi γ) y := by
  rw [(psi_deriv γ y hγ hy hA).deriv]
  have hB : 0 < (γ - 1) * y + 2 := by nlinarith
  have : 0 < (y - 1) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hy1)))
  have hg : 0 < γ - 1 := by linarith
  positivity

lemma psi_gt (γ y : ℝ) (hγ : 1 < γ) (hy : 1 < y) : psi γ 1 < psi γ y := by
  have hD : ∀ x ∈ Set.Ici (1 : ℝ), 0 < x ∧ 0 < 2 * γ * x - γ + 1 := by
    intro x hx; simp only [Set.mem_Ici] at hx; constructor <;> nlinarith
  have hm := strictMonoOn_of_deriv_pos (convex_Ici 1) (psi_cont γ hγ _ hD) (fun x hx => by
    rw [interior_Ici, Set.mem_Ioi] at hx
    exact psi_pos_deriv γ x hγ (by linarith) (by nlinarith) hx.ne')
  exact hm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy.le) hy

lemma psi_lt (γ y : ℝ) (hγ : 1 < γ) (hy : y < 1) (hy0 : 0 < y) (hA : 0 < 2 * γ * y - γ + 1) :
    psi γ y < psi γ 1 := by
  have hD' : ∀ x ∈ Set.Icc y 1, 0 < x ∧ 0 < 2 * γ * x - γ + 1 := by
    intro x hx; simp only [Set.mem_Icc] at hx; constructor <;> nlinarith
  have hm' := strictMonoOn_of_deriv_pos (convex_Icc y 1) (psi_cont γ hγ _ hD') (fun x hx => by
    rw [interior_Icc, Set.mem_Ioo] at hx
    exact psi_pos_deriv γ x hγ (by linarith) (by nlinarith) hx.2.ne)
  exact hm' (Set.left_mem_Icc.2 hy.le) (Set.right_mem_Icc.2 hy.le) hy

end LU3EntropyHelpers

open LU3EntropyHelpers in
theorem solution
    (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) (hγ : 1 < γ)
    (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) (hp₁ : 0 < p₁)
    (hρ₂ : 0 < ρ₂) (hu₂ : 0 < u₂) (hp₂ : 0 < p₂)
    (hRH : RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂)
    (hshock : (ρ₂, u₂, p₂) ≠ (ρ₁, u₁, p₁)) :
    (1 < machNumber γ ρ₁ u₁ p₁ → 0 < entropyJumpOverCv γ ρ₁ p₁ ρ₂ p₂) ∧
    (machNumber γ ρ₁ u₁ p₁ < 1 → entropyJumpOverCv γ ρ₁ p₁ ρ₂ p₂ < 0) := by
  have hg1 : 0 < γ - 1 := by linarith
  have hg2 : 0 < γ + 1 := by linarith
  have hγ0 : 0 < γ := by linarith
  obtain ⟨e1, e2, e3⟩ := hRH
  unfold perfectGasEnthalpy at e3
  have hmom : p₂ = p₁ + (ρ₁ * u₁) * (u₁ - u₂) := by
    have : ρ₂ * u₂ ^ 2 = (ρ₁ * u₁) * u₂ := by rw [← e1]; ring
    nlinarith
  have e3' : (ρ₁ * u₁) * (u₂ ^ 2 / 2) + γ / (γ - 1) * p₂ * u₂
      = (ρ₁ * u₁) * (u₁ ^ 2 / 2) + γ / (γ - 1) * p₁ * u₁ := by
    have a : ρ₂ * u₂ * (u₂ ^ 2 / 2 + γ / (γ - 1) * (p₂ / ρ₂))
        = ρ₂ * u₂ * (u₂ ^ 2 / 2) + γ / (γ - 1) * p₂ * u₂ := by field_simp
    have b : ρ₁ * u₁ * (u₁ ^ 2 / 2 + γ / (γ - 1) * (p₁ / ρ₁))
        = ρ₁ * u₁ * (u₁ ^ 2 / 2) + γ / (γ - 1) * p₁ * u₁ := by field_simp
    rw [a, b, e1] at e3; exact e3
  have key : (u₂ - u₁) * ((γ - 1) * (ρ₁ * u₁) * u₁ + 2 * γ * p₁ - (γ + 1) * (ρ₁ * u₁) * u₂) = 0 := by
    rw [hmom] at e3'
    field_simp at e3'
    linear_combination e3'
  have hu : (γ + 1) * (ρ₁ * u₁) * u₂ = (γ - 1) * (ρ₁ * u₁) * u₁ + 2 * γ * p₁ := by
    rcases mul_eq_zero.1 key with h | h
    · exfalso; apply hshock
      have hu' : u₂ = u₁ := by linarith
      have hr : ρ₂ = ρ₁ := by
        rw [hu'] at e1; exact mul_right_cancel₀ hu₁.ne' e1
      have hp : p₂ = p₁ := by rw [hmom, hu']; ring
      rw [hu', hr, hp]
    · linarith
  set y := u₁ ^ 2 * ρ₁ / (γ * p₁) with hy
  have hy0 : 0 < y := by positivity
  have hM : machNumber γ ρ₁ u₁ p₁ ^ 2 = y := by
    unfold machNumber soundSpeed soundSpeedSq
    rw [div_pow, Real.sq_sqrt (by positivity), hy]
    field_simp
  have hM0 : 0 < machNumber γ ρ₁ u₁ p₁ := by
    unfold machNumber soundSpeed soundSpeedSq; positivity
  have hP : p₂ / p₁ = (2 * γ * y - γ + 1) / (γ + 1) := by
    have hu2 : u₂ = ((γ - 1) * (ρ₁ * u₁) * u₁ + 2 * γ * p₁) / ((γ + 1) * (ρ₁ * u₁)) := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [hmom, hu2, hy]
    field_simp
    ring
  have hR : ρ₂ / ρ₁ = (γ + 1) * y / ((γ - 1) * y + 2) := by
    have hr2 : ρ₂ = ρ₁ * u₁ / u₂ := by rw [eq_div_iff hu₂.ne']; exact e1
    have hu2 : u₂ = ((γ - 1) * (ρ₁ * u₁) * u₁ + 2 * γ * p₁) / ((γ + 1) * (ρ₁ * u₁)) := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [hr2, hu2, hy]
    field_simp
  have hA : 0 < 2 * γ * y - γ + 1 := by
    have : 0 < p₂ / p₁ := by positivity
    rw [hP] at this
    exact (div_pos_iff_of_pos_right hg2).1 this
  have hB : 0 < (γ - 1) * y + 2 := by nlinarith
  have hE : entropyJumpOverCv γ ρ₁ p₁ ρ₂ p₂ = psi γ y - psi γ 1 := by
    unfold entropyJumpOverCv
    rw [psi_one, hP, hR, Real.log_div hA.ne' hg2.ne', Real.log_div (by positivity) hB.ne',
      Real.log_mul hg2.ne' hy0.ne']
    unfold psi
    ring
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : 1 < y := by rw [← hM]; nlinarith
    rw [hE]; linarith [psi_gt γ y hγ this]
  · have : y < 1 := by rw [← hM]; nlinarith
    rw [hE]; linarith [psi_lt γ y hγ this hy0 hA]
