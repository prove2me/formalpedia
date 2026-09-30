-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8AnalyticCoefficientBoxes
-- name    : CK_GeneralCK_Certificates_E8AnalyticCoefficientBoxes
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:58:27.595116+00:00
-- url     : https://prove2.me/theorems/5c57ba2a-5277-43e4-b511-2679b5fae5fe
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8AnalyticCoefficientBoxes` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8AnalyticCoefficientBoxes` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8AnalyticCoefficientBoxes` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8AnalyticCoefficientBoxes (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8AnalyticCoefficientBoxes.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8AnalyticTaylor17
import Definitions.Def_CK_GeneralCK_Certificates_E8OriginRemainder
import Definitions.Def_CK_GeneralCK_Certificates_DyadicLogSeries

-- ===== source module GeneralCK.Certificates.E8AnalyticCoefficientBoxes =====
section

/-!
# Analytic handoff for the E8 source coefficient boxes

The source boxes are represented by their exact rational midpoints and half
widths.  The analytic enclosure obligations are isolated in eight fields;
oddness discharges every intervening even coefficient automatically.
-/

namespace GeneralCK.Certificates.E8AnalyticCoefficientBoxes

open E8AnalyticGerm E8AnalyticTaylor17
open E8OriginRemainder

def sourceBox : ℕ → RatBox
  | 1 => a1 | 3 => a3 | 5 => a5 | 7 => a7
  | 9 => a9 | 11 => a11 | 13 => a13 | 15 => a15
  | _ => ⟨0, 0⟩

def sourceCenter (n : ℕ) : ℚ := ((sourceBox n).lo + (sourceBox n).hi) / 2
def sourceHalfWidth (n : ℕ) : ℚ := ((sourceBox n).hi - (sourceBox n).lo) / 2

/-- The eight concrete analytic enclosure obligations. -/
structure OddQCoefficientsInSourceBoxes : Prop where
  c1 : ‖qTaylorCoeff 1 - (sourceCenter 1 : ℂ)‖ ≤ (sourceHalfWidth 1 : ℝ)
  c3 : ‖qTaylorCoeff 3 - (sourceCenter 3 : ℂ)‖ ≤ (sourceHalfWidth 3 : ℝ)
  c5 : ‖qTaylorCoeff 5 - (sourceCenter 5 : ℂ)‖ ≤ (sourceHalfWidth 5 : ℝ)
  c7 : ‖qTaylorCoeff 7 - (sourceCenter 7 : ℂ)‖ ≤ (sourceHalfWidth 7 : ℝ)
  c9 : ‖qTaylorCoeff 9 - (sourceCenter 9 : ℂ)‖ ≤ (sourceHalfWidth 9 : ℝ)
  c11 : ‖qTaylorCoeff 11 - (sourceCenter 11 : ℂ)‖ ≤ (sourceHalfWidth 11 : ℝ)
  c13 : ‖qTaylorCoeff 13 - (sourceCenter 13 : ℂ)‖ ≤ (sourceHalfWidth 13 : ℝ)
  c15 : ‖qTaylorCoeff 15 - (sourceCenter 15 : ℂ)‖ ≤ (sourceHalfWidth 15 : ℝ)

/-- Remaining nonlinear coefficient enclosures after the linear coefficient
is proved analytically below. -/
structure HigherOddQCoefficientsInSourceBoxes : Prop where
  c3 : ‖qTaylorCoeff 3 - (sourceCenter 3 : ℂ)‖ ≤ (sourceHalfWidth 3 : ℝ)
  c5 : ‖qTaylorCoeff 5 - (sourceCenter 5 : ℂ)‖ ≤ (sourceHalfWidth 5 : ℝ)
  c7 : ‖qTaylorCoeff 7 - (sourceCenter 7 : ℂ)‖ ≤ (sourceHalfWidth 7 : ℝ)
  c9 : ‖qTaylorCoeff 9 - (sourceCenter 9 : ℂ)‖ ≤ (sourceHalfWidth 9 : ℝ)
  c11 : ‖qTaylorCoeff 11 - (sourceCenter 11 : ℂ)‖ ≤ (sourceHalfWidth 11 : ℝ)
  c13 : ‖qTaylorCoeff 13 - (sourceCenter 13 : ℂ)‖ ≤ (sourceHalfWidth 13 : ℝ)
  c15 : ‖qTaylorCoeff 15 - (sourceCenter 15 : ℂ)‖ ≤ (sourceHalfWidth 15 : ℝ)

/-- The linear source box is discharged directly by the kernel-checked
atanh series for `log 2`; it is not an additional certificate premise. -/
theorem qCoefficient_one_in_sourceBox :
    ‖qTaylorCoeff 1 - (sourceCenter 1 : ℂ)‖ ≤ (sourceHalfWidth 1 : ℝ) := by
  have hl := Real.sum_range_le_log_div (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 60
  have hu := Real.log_div_le_sum_range_add (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 60
  norm_num [Finset.sum_range_succ] at hl hu
  rw [qTaylorCoeff_one]
  have heq : (Real.log 2 : ℂ) / 8 - (sourceCenter 1 : ℂ) =
      ((Real.log 2 / 8 - (sourceCenter 1 : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_le]
  norm_num [sourceCenter, sourceHalfWidth, sourceBox, a1]
  constructor <;> linarith

theorem HigherOddQCoefficientsInSourceBoxes.toOdd
    (h : HigherOddQCoefficientsInSourceBoxes) : OddQCoefficientsInSourceBoxes :=
  ⟨qCoefficient_one_in_sourceBox, h.c3, h.c5, h.c7, h.c9, h.c11, h.c13, h.c15⟩

/-- Odd source enclosures plus analytic oddness cover every coefficient of
the degree-15 polynomial. -/
theorem all_coefficients_enclosed (h : OddQCoefficientsInSourceBoxes)
    {n : ℕ} (hn : n < 16) :
    ‖qTaylorCoeff n - (sourceCenter n : ℂ)‖ ≤ (sourceHalfWidth n : ℝ) := by
  interval_cases n <;> first
  | exact h.c1 | exact h.c3 | exact h.c5 | exact h.c7
  | exact h.c9 | exact h.c11 | exact h.c13 | exact h.c15
  | simpa [sourceCenter, sourceHalfWidth, sourceBox] using
      qTaylorCoeff_eq_zero_of_even (show Even 0 by decide)
  | simpa [sourceCenter, sourceHalfWidth, sourceBox] using
      qTaylorCoeff_eq_zero_of_even (show Even 2 by decide)
  | simpa [sourceCenter, sourceHalfWidth, sourceBox] using
      qTaylorCoeff_eq_zero_of_even (show Even 4 by decide)
  | simpa [sourceCenter, sourceHalfWidth, sourceBox] using
      qTaylorCoeff_eq_zero_of_even (show Even 6 by decide)
  | simpa [sourceCenter, sourceHalfWidth, sourceBox] using
      qTaylorCoeff_eq_zero_of_even (show Even 8 by decide)
  | simpa [sourceCenter, sourceHalfWidth, sourceBox] using
      qTaylorCoeff_eq_zero_of_even (show Even 10 by decide)
  | simpa [sourceCenter, sourceHalfWidth, sourceBox] using
      qTaylorCoeff_eq_zero_of_even (show Even 12 by decide)
  | simpa [sourceCenter, sourceHalfWidth, sourceBox] using
      qTaylorCoeff_eq_zero_of_even (show Even 14 by decide)

/-- Exact rational coefficient-error budget on the source radius. -/
def coefficientErrorBudget : ℚ :=
  ∑ n ∈ Finset.range 16, radius ^ n * sourceHalfWidth n

theorem coefficientErrorBudget_lt : coefficientErrorBudget < 1 / 10 ^ 50 := by
  norm_num [coefficientErrorBudget, sourceHalfWidth, sourceBox, radius,
    a1, a3, a5, a7, a9, a11, a13, a15, Finset.sum_range_succ]

/-- The exact source boxes bound the whole degree-15 coefficient-error
polynomial on `‖z‖ ≤ 0.08`. -/
theorem polynomial_coefficient_error_le
    (h : OddQCoefficientsInSourceBoxes) {z : ℂ}
    (hz : ‖z‖ ≤ (radius : ℝ)) :
    ‖∑ n ∈ Finset.range 16,
        z ^ n * (qTaylorCoeff n - (sourceCenter n : ℂ))‖ ≤
      (coefficientErrorBudget : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range 16,
        ‖z ^ n * (qTaylorCoeff n - (sourceCenter n : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range 16,
        (radius : ℝ) ^ n * (sourceHalfWidth n : ℝ) := by
      gcongr with n hn
      rw [norm_mul, norm_pow]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz n)
        (all_coefficients_enclosed h (Finset.mem_range.mp hn))
        (norm_nonneg _) (pow_nonneg (by norm_num [radius]) _)
    _ = (coefficientErrorBudget : ℝ) := by
      norm_cast

/-- Complete degree-15 source-center handoff.  After the seven nonlinear
coefficient boxes are established, the displayed error is below the exact
checked budget and the only remaining functional term is the order-17
analytic tail. -/
theorem exists_source_center_remainder
    (h : HigherOddQCoefficientsInSourceBoxes) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧
      (∀ z, qGerm z =
        (∑ n ∈ Finset.range 16, z ^ n * (sourceCenter n : ℂ)) +
        (∑ n ∈ Finset.range 16,
          z ^ n * (qTaylorCoeff n - (sourceCenter n : ℂ))) +
        z ^ 17 * r z) ∧
      (∀ z, ‖z‖ ≤ (radius : ℝ) →
        ‖∑ n ∈ Finset.range 16,
          z ^ n * (qTaylorCoeff n - (sourceCenter n : ℂ))‖ ≤
            (coefficientErrorBudget : ℝ)) := by
  obtain ⟨r, hr, heq⟩ := exists_degree15_odd_remainder_around
    (fun n => (sourceCenter n : ℂ))
  refine ⟨r, hr, heq, ?_⟩
  intro z hz
  exact polynomial_coefficient_error_le h.toOdd hz

end GeneralCK.Certificates.E8AnalyticCoefficientBoxes

end


