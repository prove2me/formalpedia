-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8HigherRationalTrace
-- name    : CK_GeneralCK_Certificates_E8HigherRationalTrace
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:14:47.279532+00:00
-- url     : https://prove2.me/theorems/761c11bc-976a-48b5-9efe-adbb9c133fd8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8HigherRationalTrace` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8HigherRationalTrace` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8HigherRationalTrace` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8HigherRationalTrace (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8HigherRationalTrace.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8HigherSourceBoxBridge

-- ===== source module GeneralCK.Certificates.E8HigherRationalTrace =====
section

/-! Exact real formulas and rational enclosures for the higher E8 inverse trace. -/

namespace GeneralCK.Certificates.E8HigherRationalTrace

open E8AnalyticGerm E8AnalyticCoefficientBoxes E8OriginRemainder
open E8AnalyticInverseRecurrence E8HigherSourceBoxBridge

def logCenter : ℚ :=
  693147180559945309417232121458176568075500134360255254120680 / 10^60

theorem log_two_close :
    |Real.log 2 - (logCenter : ℝ)| ≤ (1 / 10^59 : ℝ) := by
  have hl := Real.sum_range_le_log_div (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 70
  have hu := Real.log_div_le_sum_range_add (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 70
  norm_num [Finset.sum_range_succ] at hl hu
  rw [abs_le]
  norm_num [logCenter]
  constructor <;> linarith

noncomputable def q7Formula (L : ℝ) : ℝ :=
  -L^4 * (584*L^3 - 2730*L^2 + 3780*L - 1575) / 20643840
noncomputable def q9Formula (L : ℝ) : ℝ :=
  L^5 * (56768*L^4 - 358050*L^3 + 763875*L^2 - 661500*L + 198450) /
    23781703680
noncomputable def q11Formula (L : ℝ) : ℝ :=
  -L^6 * (4380256*L^5 - 34864236*L^4 + 101226510*L^3 - 135394875*L^2 +
    84199500*L - 19646550) / 20927899238400
noncomputable def q13Formula (L : ℝ) : ℝ :=
  L^7 * (983051392*L^6 - 9463894440*L^5 + 34914199320*L^4 -
    63733044375*L^3 + 61183722600*L^2 - 29499294825*L + 5618913300) /
    52236036499046400
noncomputable def q15Formula (L : ℝ) : ℝ :=
  -L^8 * (37788392576*L^7 - 427290803472*L^6 + 1917356641200*L^5 -
    4459512026970*L^4 + 5845031992800*L^3 - 4343647007700*L^2 +
    1704403701000*L - 273922023375) / 21939135329599488000

noncomputable def polyEval (c : ℕ → ℚ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range N, (c i : ℝ) * x ^ i

theorem abs_pow_sub_pow_le_delta {x y : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (n : ℕ) :
    |x ^ n - y ^ n| ≤ n * |x - y| := by
  calc
    |x ^ n - y ^ n| ≤ |x - y| * n * max |x| |y| ^ (n - 1) :=
      abs_pow_sub_pow_le x y n
    _ ≤ |x - y| * n * 1 := by
      gcongr
      exact pow_le_one₀ ((abs_nonneg x).trans (le_max_left _ _)) (max_le hx hy)
    _ = n * |x - y| := by ring

theorem polyEval_lipschitz (c : ℕ → ℚ) (N : ℕ) {x y : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |polyEval c N x - polyEval c N y| ≤
      (∑ i ∈ Finset.range N, |(c i : ℝ)| * i) * |x - y| := by
  rw [polyEval, polyEval, ← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ Finset.range N, ((c i : ℝ) * x ^ i - (c i : ℝ) * y ^ i)| ≤
        ∑ i ∈ Finset.range N,
          |(c i : ℝ) * x ^ i - (c i : ℝ) * y ^ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, |(c i : ℝ)| * (i * |x - y|) := by
      gcongr with i hi
      rw [← mul_sub, abs_mul]
      gcongr
      exact abs_pow_sub_pow_le_delta hx hy i
    _ = (∑ i ∈ Finset.range N, |(c i : ℝ)| * i) * |x - y| := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

def q7Coeff : ℕ → ℚ
  | 4 => 1575 / 20643840 | 5 => -3780 / 20643840
  | 6 => 2730 / 20643840 | 7 => -584 / 20643840 | _ => 0
def q9Coeff : ℕ → ℚ
  | 5 => 198450 / 23781703680 | 6 => -661500 / 23781703680
  | 7 => 763875 / 23781703680 | 8 => -358050 / 23781703680
  | 9 => 56768 / 23781703680 | _ => 0
def q11Coeff : ℕ → ℚ
  | 6 => 19646550 / 20927899238400 | 7 => -84199500 / 20927899238400
  | 8 => 135394875 / 20927899238400 | 9 => -101226510 / 20927899238400
  | 10 => 34864236 / 20927899238400 | 11 => -4380256 / 20927899238400 | _ => 0
def q13Coeff : ℕ → ℚ
  | 7 => 5618913300 / 52236036499046400 | 8 => -29499294825 / 52236036499046400
  | 9 => 61183722600 / 52236036499046400 | 10 => -63733044375 / 52236036499046400
  | 11 => 34914199320 / 52236036499046400 | 12 => -9463894440 / 52236036499046400
  | 13 => 983051392 / 52236036499046400 | _ => 0
def q15Coeff : ℕ → ℚ
  | 8 => 273922023375 / 21939135329599488000
  | 9 => -1704403701000 / 21939135329599488000
  | 10 => 4343647007700 / 21939135329599488000
  | 11 => -5845031992800 / 21939135329599488000
  | 12 => 4459512026970 / 21939135329599488000
  | 13 => -1917356641200 / 21939135329599488000
  | 14 => 427290803472 / 21939135329599488000
  | 15 => -37788392576 / 21939135329599488000 | _ => 0

theorem q7Formula_eq_polyEval (x : ℝ) : q7Formula x = polyEval q7Coeff 8 x := by
  norm_num [q7Formula, polyEval, q7Coeff, Finset.sum_range_succ]
  ring
theorem q9Formula_eq_polyEval (x : ℝ) : q9Formula x = polyEval q9Coeff 10 x := by
  norm_num [q9Formula, polyEval, q9Coeff, Finset.sum_range_succ]
  ring
theorem q11Formula_eq_polyEval (x : ℝ) : q11Formula x = polyEval q11Coeff 12 x := by
  norm_num [q11Formula, polyEval, q11Coeff, Finset.sum_range_succ]
  ring
theorem q13Formula_eq_polyEval (x : ℝ) : q13Formula x = polyEval q13Coeff 14 x := by
  norm_num [q13Formula, polyEval, q13Coeff, Finset.sum_range_succ]
  ring
theorem q15Formula_eq_polyEval (x : ℝ) : q15Formula x = polyEval q15Coeff 16 x := by
  norm_num [q15Formula, polyEval, q15Coeff, Finset.sum_range_succ]
  ring

/-- The retained exact-rational calculations only need deliberately loose
Lipschitz constants. -/
structure FormulaLipschitzTrace : Prop where
  q7 : |q7Formula (Real.log 2) - q7Formula logCenter| ≤ 1 / 10^61
  q9 : |q9Formula (Real.log 2) - q9Formula logCenter| ≤ 1 / 10^62
  q11 : |q11Formula (Real.log 2) - q11Formula logCenter| ≤ 1 / 10^62
  q13 : |q13Formula (Real.log 2) - q13Formula logCenter| ≤ 1 / 10^63
  q15 : |q15Formula (Real.log 2) - q15Formula logCenter| ≤ 1 / 10^64

theorem formulaLipschitzTrace : FormulaLipschitzTrace := by
  have hlog := log_two_close
  have hx : |Real.log 2| ≤ 1 := by
    rw [abs_of_pos (Real.log_pos (by norm_num))]
    exact (Real.log_two_lt_d9.trans (by norm_num)).le
  have hy : |(logCenter : ℝ)| ≤ 1 := by norm_num [logCenter, abs_of_nonneg]
  have bound (c : ℕ → ℚ) (N : ℕ) := polyEval_lipschitz c N hx hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hb := bound q7Coeff 8
    have hc : (∑ i ∈ Finset.range 8, |(q7Coeff i : ℝ)| * i) *
        |Real.log 2 - (logCenter : ℝ)| ≤ 1 / 10^61 := by
      calc
        _ ≤ (∑ i ∈ Finset.range 8, |(q7Coeff i : ℝ)| * i) * (1 / 10^59) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        _ ≤ _ := by norm_num [q7Coeff, Finset.sum_range_succ]
    rw [q7Formula_eq_polyEval, q7Formula_eq_polyEval]
    exact hb.trans hc
  · have hb := bound q9Coeff 10
    have hc : (∑ i ∈ Finset.range 10, |(q9Coeff i : ℝ)| * i) *
        |Real.log 2 - (logCenter : ℝ)| ≤ 1 / 10^62 := by
      calc
        _ ≤ (∑ i ∈ Finset.range 10, |(q9Coeff i : ℝ)| * i) * (1 / 10^59) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        _ ≤ _ := by norm_num [q9Coeff, Finset.sum_range_succ]
    rw [q9Formula_eq_polyEval, q9Formula_eq_polyEval]
    exact hb.trans hc
  · have hb := bound q11Coeff 12
    have hc : (∑ i ∈ Finset.range 12, |(q11Coeff i : ℝ)| * i) *
        |Real.log 2 - (logCenter : ℝ)| ≤ 1 / 10^62 := by
      calc
        _ ≤ (∑ i ∈ Finset.range 12, |(q11Coeff i : ℝ)| * i) * (1 / 10^59) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        _ ≤ _ := by norm_num [q11Coeff, Finset.sum_range_succ]
    rw [q11Formula_eq_polyEval, q11Formula_eq_polyEval]
    exact hb.trans hc
  · have hb := bound q13Coeff 14
    have hc : (∑ i ∈ Finset.range 14, |(q13Coeff i : ℝ)| * i) *
        |Real.log 2 - (logCenter : ℝ)| ≤ 1 / 10^63 := by
      calc
        _ ≤ (∑ i ∈ Finset.range 14, |(q13Coeff i : ℝ)| * i) * (1 / 10^59) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        _ ≤ _ := by norm_num [q13Coeff, Finset.sum_range_succ]
    rw [q13Formula_eq_polyEval, q13Formula_eq_polyEval]
    exact hb.trans hc
  · have hb := bound q15Coeff 16
    have hc : (∑ i ∈ Finset.range 16, |(q15Coeff i : ℝ)| * i) *
        |Real.log 2 - (logCenter : ℝ)| ≤ 1 / 10^64 := by
      calc
        _ ≤ (∑ i ∈ Finset.range 16, |(q15Coeff i : ℝ)| * i) * (1 / 10^59) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        _ ≤ _ := by norm_num [q15Coeff, Finset.sum_range_succ]
    rw [q15Formula_eq_polyEval, q15Formula_eq_polyEval]
    exact hb.trans hc

/-- Exact evaluation at the rational log center, widened by `10^-60`, lies
inside every retained source interval. -/
theorem formula_endpoints_of_lipschitz (h : FormulaLipschitzTrace) :
    ((a7.lo : ℝ) ≤ q7Formula (Real.log 2) ∧ q7Formula (Real.log 2) ≤ (a7.hi : ℝ)) ∧
    ((a9.lo : ℝ) ≤ q9Formula (Real.log 2) ∧ q9Formula (Real.log 2) ≤ (a9.hi : ℝ)) ∧
    ((a11.lo : ℝ) ≤ q11Formula (Real.log 2) ∧ q11Formula (Real.log 2) ≤ (a11.hi : ℝ)) ∧
    ((a13.lo : ℝ) ≤ q13Formula (Real.log 2) ∧ q13Formula (Real.log 2) ≤ (a13.hi : ℝ)) ∧
    ((a15.lo : ℝ) ≤ q15Formula (Real.log 2) ∧ q15Formula (Real.log 2) ≤ (a15.hi : ℝ)) := by
  rcases h with ⟨h7, h9, h11, h13, h15⟩
  rw [abs_le] at h7 h9 h11 h13 h15
  norm_num [q7Formula, q9Formula, q11Formula, q13Formula, q15Formula,
    logCenter, a7, a9, a11, a13, a15] at *
  constructor
  · constructor <;> linarith [h7.1, h7.2]
  constructor
  · constructor <;> linarith [h9.1, h9.2]
  constructor
  · constructor <;> linarith [h11.1, h11.2]
  constructor
  · constructor <;> linarith [h13.1, h13.2]
  · constructor <;> linarith [h15.1, h15.2]

/-- The remaining analytic-to-formal-series identifications.  All numerical
content has been removed from this interface. -/
structure HigherInverseStepFormulaIdentities : Prop where
  q7 : inverseStep thetaTaylorCoeff qTaylorCoeff 7 =
    (q7Formula (Real.log 2) : ℂ)
  q9 : inverseStep thetaTaylorCoeff qTaylorCoeff 9 =
    (q9Formula (Real.log 2) : ℂ)
  q11 : inverseStep thetaTaylorCoeff qTaylorCoeff 11 =
    (q11Formula (Real.log 2) : ℂ)
  q13 : inverseStep thetaTaylorCoeff qTaylorCoeff 13 =
    (q13Formula (Real.log 2) : ℂ)
  q15 : inverseStep thetaTaylorCoeff qTaylorCoeff 15 =
    (q15Formula (Real.log 2) : ℂ)

/-- The proof-producing rational trace constructs the complete retained-box
certificate once the five finite analytic coefficient identities are known. -/
noncomputable def retainedCertificate_of_formula_identities
    (h : HigherInverseStepFormulaIdentities) :
    HigherInverseStepInRetainedBoxes := by
  have hb := formula_endpoints_of_lipschitz formulaLipschitzTrace
  exact
    { x7 := q7Formula (Real.log 2)
      eq7 := h.q7
      lo7 := hb.1.1
      hi7 := hb.1.2
      x9 := q9Formula (Real.log 2)
      eq9 := h.q9
      lo9 := hb.2.1.1
      hi9 := hb.2.1.2
      x11 := q11Formula (Real.log 2)
      eq11 := h.q11
      lo11 := hb.2.2.1.1
      hi11 := hb.2.2.1.2
      x13 := q13Formula (Real.log 2)
      eq13 := h.q13
      lo13 := hb.2.2.2.1.1
      hi13 := hb.2.2.2.1.2
      x15 := q15Formula (Real.log 2)
      eq15 := h.q15
      lo15 := hb.2.2.2.2.1
      hi15 := hb.2.2.2.2.2 }

/-- Consequently the five source boxes require no additional numerical
assumptions after the formal-series identities are supplied. -/
theorem higher_source_boxes_of_formula_identities
    (h : HigherInverseStepFormulaIdentities) :
    (‖qTaylorCoeff 7 - (sourceCenter 7 : ℂ)‖ ≤
        (sourceHalfWidth 7 : ℝ)) ∧
    (‖qTaylorCoeff 9 - (sourceCenter 9 : ℂ)‖ ≤
        (sourceHalfWidth 9 : ℝ)) ∧
    (‖qTaylorCoeff 11 - (sourceCenter 11 : ℂ)‖ ≤
        (sourceHalfWidth 11 : ℝ)) ∧
    (‖qTaylorCoeff 13 - (sourceCenter 13 : ℂ)‖ ≤
        (sourceHalfWidth 13 : ℝ)) ∧
    (‖qTaylorCoeff 15 - (sourceCenter 15 : ℂ)‖ ≤
        (sourceHalfWidth 15 : ℝ)) :=
  higher_source_boxes_of_retained_endpoint_checks
    (retainedCertificate_of_formula_identities h)

end GeneralCK.Certificates.E8HigherRationalTrace

end


