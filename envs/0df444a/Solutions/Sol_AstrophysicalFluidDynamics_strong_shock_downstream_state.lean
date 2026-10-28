-- Prove2me | solution 1 for AstrophysicalFluidDynamics.strong_shock_downstream_state
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T11:56:53.203995+00:00
-- url     : https://prove2.me/submissions/435693b0-30db-48fc-8426-eba8b6a16c51

import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs
import Mathlib

open Filter Topology
open AstrophysicalFluidDynamics

namespace LU3ShockHelpers

lemma ev (f : ℝ → ℝ) (hf : ContinuousAt f 0) (h0 : f 0 = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p : ℝ, 0 < p → p < δ → |f p| < ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hf ε hε
  refine ⟨δ, hδ, fun p hp hpd => ?_⟩
  have := h (x := p) (by rw [Real.dist_eq, sub_zero, abs_of_pos hp]; exact hpd)
  rwa [Real.dist_eq, h0, sub_zero] at this

end LU3ShockHelpers

open LU3ShockHelpers in
theorem solution
    (γ ρ₁ u₁ : ℝ) (hγ : 1 < γ) (hρ₁ : 0 < ρ₁) (hu₁ : 0 < u₁) :
    ∀ ε > 0, ∃ δ > 0, ∀ p₁ ρ₂ u₂ p₂ : ℝ, 0 < p₁ → p₁ < δ →
      0 < ρ₂ → 0 < u₂ → 0 < p₂ →
      RankineHugoniot γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ → (ρ₂, u₂, p₂) ≠ (ρ₁, u₁, p₁) →
        |ρ₂ - (γ + 1) / (γ - 1) * ρ₁| < ε ∧
        |(u₂ - u₁) - 2 * (-u₁) / (γ + 1)| < ε ∧
        |p₂ - 2 * ρ₁ * (-u₁) ^ 2 / (γ + 1)| < ε ∧
        |perfectGasInternalEnergy γ p₂ ρ₂ - 2 * (-u₁) ^ 2 / (γ + 1) ^ 2| < ε := by
  intro ε hε
  have hj0 : 0 < ρ₁ * u₁ := mul_pos hρ₁ hu₁
  have hg1 : 0 < γ - 1 := by linarith
  have hg2 : 0 < γ + 1 := by linarith
  obtain ⟨U, hU⟩ : ∃ U : ℝ → ℝ, U = fun p => ((γ - 1) * u₁ + 2 * γ * p / (ρ₁ * u₁)) / (γ + 1) :=
    ⟨_, rfl⟩
  have hUc : Continuous U := by rw [hU]; fun_prop
  have hU0 : U 0 ≠ 0 := by simp only [hU]; positivity
  have hU0' : U 0 = (γ - 1) * u₁ / (γ + 1) := by simp only [hU]; ring
  obtain ⟨δ1, hδ1, h1⟩ := ev (fun p => (ρ₁ * u₁) / U p - (γ + 1) / (γ - 1) * ρ₁)
    ((continuousAt_const.div hUc.continuousAt hU0).sub continuousAt_const)
    (by rw [hU0']; field_simp; ring) ε hε
  obtain ⟨δ2, hδ2, h2⟩ := ev (fun p => (U p - u₁) - 2 * (-u₁) / (γ + 1))
    (by rw [hU]; fun_prop) (by rw [hU0']; field_simp; ring) ε hε
  obtain ⟨δ3, hδ3, h3⟩ := ev (fun p => (p + (ρ₁ * u₁) * (u₁ - U p)) - 2 * ρ₁ * (-u₁) ^ 2 / (γ + 1))
    (by rw [hU]; fun_prop) (by rw [hU0']; field_simp; ring) ε hε
  obtain ⟨δ4, hδ4, h4⟩ := ev (fun p => perfectGasInternalEnergy γ (p + (ρ₁ * u₁) * (u₁ - U p)) ((ρ₁ * u₁) / U p)
      - 2 * (-u₁) ^ 2 / (γ + 1) ^ 2)
    (by
      unfold perfectGasInternalEnergy
      refine ContinuousAt.sub (ContinuousAt.div (by rw [hU]; fun_prop)
        (continuousAt_const.mul (continuousAt_const.div hUc.continuousAt hU0)) ?_)
        continuousAt_const
      rw [hU0']; positivity)
    (by unfold perfectGasInternalEnergy; rw [hU0']; field_simp; ring) ε hε
  refine ⟨min (min δ1 δ2) (min δ3 δ4), by positivity, ?_⟩
  intro p₁ ρ₂ u₂ p₂ hp₁ hpδ hρ₂ hu₂ hp₂ hRH hne
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
  have hu : u₂ = U p₁ := by
    rcases mul_eq_zero.1 key with h | h
    · exfalso; apply hne
      have hu' : u₂ = u₁ := by linarith
      have hr : ρ₂ = ρ₁ := by
        rw [hu'] at e1; exact mul_right_cancel₀ hu₁.ne' e1
      have hp : p₂ = p₁ := by rw [hmom, hu']; ring
      rw [hu', hr, hp]
    · simp only [hU]; field_simp; linarith
  have hr : ρ₂ = (ρ₁ * u₁) / U p₁ := by
    rw [← hu, eq_div_iff hu₂.ne']; exact e1
  rw [hmom, hr, hu]
  refine ⟨h1 p₁ hp₁ (by
      have := min_le_left (min δ1 δ2) (min δ3 δ4); have := min_le_left δ1 δ2; linarith),
    h2 p₁ hp₁ (by
      have := min_le_left (min δ1 δ2) (min δ3 δ4); have := min_le_right δ1 δ2; linarith),
    h3 p₁ hp₁ (by
      have := min_le_right (min δ1 δ2) (min δ3 δ4); have := min_le_left δ3 δ4; linarith),
    h4 p₁ hp₁ (by
      have := min_le_right (min δ1 δ2) (min δ3 δ4); have := min_le_right δ3 δ4; linarith)⟩
