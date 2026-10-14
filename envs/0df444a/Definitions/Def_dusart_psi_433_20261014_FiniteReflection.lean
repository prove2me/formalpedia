-- Prove2me | Definitions.Def_dusart_psi_433_20261014_FiniteReflection
-- name    : dusart_psi_433_20261014_FiniteReflection
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:34:08.814983+00:00
-- url     : https://prove2.me/theorems/4a6565d0-9fd0-4c11-99d0-ee04383c176a
-- title:
--   Dusart smoothing: Finite Reflection
-- statement:
--   This module gives the complete finite reflection component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ReflectedPowers
noncomputable section
namespace DusartSmoothing
open Complex Real

lemma finite_reflected_zero_power_sum (R x : ℝ) (hR : 0 < R) (hx : 1 < x)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ)
    (hreflect : ∀ ρ ∈ Z, 1 - starRingEnd ℂ ρ ∈ Z)
    (w : ℝ → ℝ) (hw : ∀ ρ ∈ Z, 0 ≤ w ρ.im) :
    2 * (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * w ρ.im * (‖(x : ℂ)^ρ‖ / x)) ≤
      (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * w ρ.im *
        Real.exp (-(X R x)^2 / Real.log |ρ.im|)) +
      Real.sqrt (1 / x) * ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * w ρ.im := by
  classical
  let τ : ℂ → ℂ := fun ρ => 1 - starRingEnd ℂ ρ
  have hinv : Function.Involutive τ := by
    intro ρ
    simp [τ]
  have him : ∀ ρ : ℂ, (τ ρ).im = ρ.im := by intro ρ; simp [τ]
  have himage : Z.image τ = Z := by
    ext ρ
    constructor
    · intro h
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp h
      exact hreflect σ hσ
    · intro h
      exact Finset.mem_image.mpr ⟨τ ρ, hreflect ρ h, hinv ρ⟩
  have he : (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * w ρ.im * (‖(x : ℂ)^ρ‖ / x)) =
      ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * w ρ.im * (‖(x : ℂ)^(τ ρ)‖ / x) := by
    conv_lhs => rw [← himage]
    rw [Finset.sum_image (fun a _ b _ h => hinv.injective h)]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [show RvM.zeroMult (τ ρ) = RvM.zeroMult ρ from RvM.zeroMult_reflect ρ (hZ ρ hρ), him]
  have hterm : ∀ ρ ∈ Z,
      (RvM.zeroMult ρ : ℝ) * w ρ.im * (‖(x : ℂ)^ρ‖ / x + ‖(x : ℂ)^(τ ρ)‖ / x) ≤
      (RvM.zeroMult ρ : ℝ) * w ρ.im *
        (Real.exp (-(X R x)^2 / Real.log |ρ.im|) + Real.sqrt (1 / x)) := by
    intro ρ hρ
    exact mul_le_mul_of_nonneg_left (reflected_zero_power_majorant R x hR hx hzero ρ (hZ ρ hρ))
      (mul_nonneg (Nat.cast_nonneg _) (hw ρ hρ))
  have hs := Finset.sum_le_sum hterm
  simp_rw [mul_add] at hs
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hs
  have hc : (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * w ρ.im * Real.sqrt (1 / x)) =
      Real.sqrt (1 / x) * ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * w ρ.im := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    ring
  rw [hc, ← he] at hs
  linarith

lemma zero_window_reflection {a b : ℝ} (ha : 0 < a) (ρ : ℂ)
    (hρ : ρ ∈ (RvM.finite_zero_window (b := b) ha).toFinset) :
    1 - starRingEnd ℂ ρ ∈ (RvM.finite_zero_window (b := b) ha).toFinset := by
  rw [Set.Finite.mem_toFinset] at hρ ⊢
  exact ⟨RvM.nontrivial_zero_reflect hρ.1, by simpa using hρ.2.1, by simpa using hρ.2.2⟩

end DusartSmoothing


