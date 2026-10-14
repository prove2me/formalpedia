-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZeroAbel
-- name    : dusart_psi_433_20261014_ZeroAbel
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:32:48.595751+00:00
-- url     : https://prove2.me/theorems/3831615f-b450-411c-ae45-a735280fdb75
-- title:
--   Dusart smoothing: Zero Abel
-- statement:
--   This module gives the complete zero abel component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_SymmetricWindows
import Definitions.Def_dusart_psi_433_20261014_ArithmeticKernels
noncomputable section
namespace DusartSmoothing
open Set MeasureTheory

lemma integral_step_mul_deriv (a b c : ℝ) (hc : a ≤ c ∧ c ≤ b)
    (g g' : ℝ → ℝ) (hcont : ContinuousOn g' (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t) :
    (∫ t in a..b, primeStep c t * g' t) = g b - g c := by
  have hab : a ≤ b := hc.1.trans hc.2
  have hsub₁ : uIcc a c ⊆ Icc a b := by
    rw [uIcc_of_le hc.1]
    intro t ht
    exact ⟨ht.1, ht.2.trans hc.2⟩
  have hsub₂ : uIcc c b ⊆ Icc a b := by
    rw [uIcc_of_le hc.2]
    intro t ht
    exact ⟨hc.1.trans ht.1, ht.2⟩
  have hi₁ : IntervalIntegrable (fun t => primeStep c t * g' t) volume a c :=
    ((primeStep_mono c).intervalIntegrable (μ := volume)).mul_continuousOn (hcont.mono hsub₁)
  have hi₂ : IntervalIntegrable (fun t => primeStep c t * g' t) volume c b :=
    ((primeStep_mono c).intervalIntegrable (μ := volume)).mul_continuousOn (hcont.mono hsub₂)
  have hl : (∫ t in a..c, primeStep c t * g' t) = 0 := by
    calc _ = ∫ _ in a..c, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hc.1
          intro t ht
          simp only [primeStep, if_neg (not_le.mpr ht.2), zero_mul]
      _ = 0 := intervalIntegral.integral_zero
  have hu : (∫ t in c..b, primeStep c t * g' t) = g b - g c := by
    calc _ = ∫ t in c..b, g' t := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hc.2] at ht
          simp only [primeStep, if_pos ht.1, one_mul]
      _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hderiv t (hsub₂ ht)) (hcont.mono hsub₂).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂, hl, hu, zero_add]

def finiteZeroCount {α : Type*} (Z : Finset α) (m : α → ℕ) (γ : α → ℝ) (t : ℝ) : ℝ :=
  ∑ ρ ∈ Z, (m ρ : ℝ) * primeStep (γ ρ) t

lemma finite_zero_summation_by_parts {α : Type*} (Z : Finset α)
    (m : α → ℕ) (γ : α → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hγ : ∀ ρ ∈ Z, a ≤ γ ρ ∧ γ ρ ≤ b)
    (g g' : ℝ → ℝ) (hcont : ContinuousOn g' (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t) :
    (∑ ρ ∈ Z, (m ρ : ℝ) * g (γ ρ)) =
      g b * (∑ ρ ∈ Z, (m ρ : ℝ)) -
        ∫ t in a..b, finiteZeroCount Z m γ t * g' t := by
  have hi : ∀ ρ ∈ Z, IntervalIntegrable
      (fun t => (m ρ : ℝ) * primeStep (γ ρ) t * g' t) volume a b := by
    intro ρ hρ
    exact (((primeStep_mono (γ ρ)).intervalIntegrable (μ := volume)).const_mul _).mul_continuousOn
      (by simpa [uIcc_of_le hab] using hcont)
  have he : (fun t => finiteZeroCount Z m γ t * g' t) =
      (fun t => ∑ ρ ∈ Z, (m ρ : ℝ) * primeStep (γ ρ) t * g' t) := by
    funext t
    rw [finiteZeroCount, Finset.sum_mul]
  rw [he, intervalIntegral.integral_finsetSum hi]
  have hval : ∀ ρ ∈ Z, (∫ t in a..b, (m ρ : ℝ) * primeStep (γ ρ) t * g' t) =
      (m ρ : ℝ) * (g b - g (γ ρ)) := by
    intro ρ hρ
    simp only [mul_assoc]
    rw [intervalIntegral.integral_const_mul,
      integral_step_mul_deriv a b (γ ρ) (hγ ρ hρ) g g' hcont hderiv]
  rw [Finset.sum_congr rfl hval]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  ring

end DusartSmoothing


