-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalMassScale
-- name    : row23_rh_supp_RHLocalMassScale
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:16:33.02336+00:00
-- url     : https://prove2.me/theorems/cc4487c5-8049-44c5-9f62-d522f0299eb4
-- title:
--   Row 23 RH support: RHLocalMassScale
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreRodrigues
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace DusartLegendreSmoothing
open Polynomial MeasureTheory intervalIntegral

theorem derivativeMass_le_scaled (m : ℕ) (δ₀ δ₁ : ℝ)
    (hδ₀ : 0 ≤ δ₀) (hδ₁ : 0 ≤ δ₁) :
    derivativeMass m δ₁ ≤ (1 + δ₁)^(m+1) * derivativeMass m δ₀ := by
  rw [derivativeMass_eq, derivativeMass_eq]
  let f : ℝ → ℝ := fun t => |((shiftedLegendre m).map (Int.castRingHom ℝ)).eval t|
  let K : ℝ := (1 + δ₁)^(m+1)
  have hf : Continuous f := (Polynomial.continuous _).abs
  have hcont0 : Continuous (fun t : ℝ => f t * (1 + δ₀*t)^(m+1)) := hf.mul (by fun_prop)
  have hcont1 : Continuous (fun t : ℝ => f t * (1 + δ₁*t)^(m+1)) := hf.mul (by fun_prop)
  have hle : (∫ t : ℝ in 0..1, f t * (1 + δ₁*t)^(m+1)) ≤
      ∫ t : ℝ in 0..1, K * (f t * (1 + δ₀*t)^(m+1)) := by
    apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      (hcont1.intervalIntegrable _ _) ((hcont0.const_mul K).intervalIntegrable _ _)
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hp1 : (1 + δ₁*t)^(m+1) ≤ K := by
      dsimp [K]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith
    have hp0 : (1:ℝ) ≤ (1 + δ₀*t)^(m+1) := by
      calc
        _ = (1:ℝ)^(m+1) := by simp
        _ ≤ (1 + δ₀*t)^(m+1) := by
          apply pow_le_pow_left₀ (by norm_num)
          nlinarith
    have hf0 : 0 ≤ f t := abs_nonneg _
    have hK : 0 ≤ K := by dsimp [K]; positivity
    calc
      f t * (1 + δ₁*t)^(m+1) ≤ f t * K := mul_le_mul_of_nonneg_left hp1 hf0
      _ ≤ (f t * K) * (1 + δ₀*t)^(m+1) := le_mul_of_one_le_right (mul_nonneg hf0 hK) hp0
      _ = K * (f t * (1 + δ₀*t)^(m+1)) := by ring
  rw [intervalIntegral.integral_const_mul] at hle
  have hc : (0:ℝ) ≤ ((2*m+1).factorial:ℝ)/(m.factorial:ℝ) := by positivity
  dsimp [f] at hle
  calc
    _ ≤ (((2*m+1).factorial:ℝ)/(m.factorial:ℝ)) *
        (K * ∫ t : ℝ in 0..1, |((shiftedLegendre m).map (Int.castRingHom ℝ)).eval t| * (1 + δ₀*t)^(m+1)) :=
      mul_le_mul_of_nonneg_left hle hc
    _ = _ := by dsimp [K]; ring
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.derivativeMass_le_scaled


