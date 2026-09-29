-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasCoefficientBounds
-- name    : CK_GeneralCK_ReflectionSmallBiasCoefficientBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:57:30.868487+00:00
-- url     : https://prove2.me/theorems/53cb1045-c2f6-409b-8dfd-f1e551e00187
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasCoefficientBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasCoefficientBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasCoefficientBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasCoefficientBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasCoefficientBounds.lean)

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- ===== source module GeneralCK.ReflectionSmallBiasCoefficientBounds =====
section

/-! # Exact interval bounds for the small-bias coefficient polynomials -/

namespace GeneralCK.Reflection.SmallBiasCoefficientBounds

structure PowerTerm where
  c : ℚ
  n : ℕ
  deriving DecidableEq, Repr

def eval {K : Type*} [Field K] [CharZero K] : List PowerTerm → K → K
  | [], _ => 0
  | p :: ps, x => (p.c : K) * x ^ p.n + eval ps x

def lowerTerm (p : PowerTerm) (l u : ℚ) : ℚ :=
  if 0 ≤ p.c then p.c * l ^ p.n else p.c * u ^ p.n

def upperTerm (p : PowerTerm) (l u : ℚ) : ℚ :=
  if 0 ≤ p.c then p.c * u ^ p.n else p.c * l ^ p.n

def lower : List PowerTerm → ℚ → ℚ → ℚ
  | [], _, _ => 0
  | p :: ps, l, u => lowerTerm p l u + lower ps l u

def upper : List PowerTerm → ℚ → ℚ → ℚ
  | [], _, _ => 0
  | p :: ps, l, u => upperTerm p l u + upper ps l u

theorem term_bounds (p : PowerTerm) {l u : ℚ} {x : ℝ}
    (hl : 0 ≤ l) (hlx : (l : ℝ) ≤ x) (hxu : x ≤ (u : ℝ)) :
    (lowerTerm p l u : ℝ) ≤ (p.c : ℝ) * x ^ p.n ∧
      (p.c : ℝ) * x ^ p.n ≤ (upperTerm p l u : ℝ) := by
  have hl' : (0 : ℝ) ≤ l := by exact_mod_cast hl
  have hx : 0 ≤ x := hl'.trans hlx
  have hlow := pow_le_pow_left₀ hl' hlx p.n
  have hupp := pow_le_pow_left₀ hx hxu p.n
  by_cases hc : 0 ≤ p.c
  · have hc' : (0 : ℝ) ≤ p.c := by exact_mod_cast hc
    simp only [lowerTerm, upperTerm, if_pos hc, Rat.cast_mul, Rat.cast_pow]
    exact ⟨mul_le_mul_of_nonneg_left hlow hc', mul_le_mul_of_nonneg_left hupp hc'⟩
  · have hc' : (p.c : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hc)
    simp only [lowerTerm, upperTerm, if_neg hc, Rat.cast_mul, Rat.cast_pow]
    exact ⟨mul_le_mul_of_nonpos_left hupp hc', mul_le_mul_of_nonpos_left hlow hc'⟩

theorem eval_bounds (ps : List PowerTerm) {l u : ℚ} {x : ℝ}
    (hl : 0 ≤ l) (hlx : (l : ℝ) ≤ x) (hxu : x ≤ (u : ℝ)) :
    (lower ps l u : ℝ) ≤ eval ps x ∧ eval ps x ≤ (upper ps l u : ℝ) := by
  induction ps with
  | nil => simp [lower, upper, eval]
  | cons p ps ih =>
    have hp := term_bounds p hl hlx hxu
    simp only [lower, upper, eval, Rat.cast_add]
    exact ⟨add_le_add hp.1 ih.1, add_le_add hp.2 ih.2⟩

theorem eval_complex_ofReal (ps : List PowerTerm) (x : ℝ) :
    eval ps (x : ℂ) = ((eval ps x : ℝ) : ℂ) := by
  induction ps with
  | nil => simp [eval]
  | cons p ps ih => simp [eval, ih]

def invLogLower : ℚ := 10000000000 / 6931471808
def invLogUpper : ℚ := 10000000000 / 6931471803

theorem inv_log_two_bounds :
    (invLogLower : ℝ) ≤ (Real.log 2)⁻¹ ∧ (Real.log 2)⁻¹ ≤ (invLogUpper : ℝ) := by
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · have hh := one_div_le_one_div_of_le hpos Real.log_two_lt_d9.le
    norm_num [invLogLower] at *
    simpa only [one_div] using hh
  · have hh := one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 0.6931471803) Real.log_two_gt_d9.le
    norm_num [invLogUpper] at *
    simpa only [one_div] using hh

theorem eval_at_inv_log_two_bounds (ps : List PowerTerm) :
    (lower ps invLogLower invLogUpper : ℝ) ≤ eval ps (Real.log 2)⁻¹ ∧
      eval ps (Real.log 2)⁻¹ ≤ (upper ps invLogLower invLogUpper : ℝ) :=
  eval_bounds ps (by norm_num [invLogLower]) inv_log_two_bounds.1 inv_log_two_bounds.2

def checkCoefficient (ps : List PowerTerm) : Bool :=
  decide (0 < lower ps invLogLower invLogUpper ∧ upper ps invLogLower invLogUpper < 1)

theorem checkCoefficient_sound {ps : List PowerTerm} (h : checkCoefficient ps = true) :
    0 < eval ps (Real.log 2)⁻¹ ∧ eval ps (Real.log 2)⁻¹ < 1 := by
  have hc : 0 < lower ps invLogLower invLogUpper ∧ upper ps invLogLower invLogUpper < 1 := by
    simpa only [checkCoefficient, decide_eq_true_eq] using h
  have hl : (0 : ℝ) < lower ps invLogLower invLogUpper := by exact_mod_cast hc.1
  have hu : (upper ps invLogLower invLogUpper : ℝ) < 1 := by exact_mod_cast hc.2
  have hh := eval_at_inv_log_two_bounds ps
  exact ⟨hl.trans_le hh.1, hh.2.trans_lt hu⟩

structure CoefficientRow where
  i : ℕ
  j : ℕ
  coefficients : List PowerTerm
  deriving DecidableEq, Repr

def checkRows (rows : List CoefficientRow) : Bool :=
  rows.all fun row => checkCoefficient row.coefficients

theorem checkRows_sound {rows : List CoefficientRow} (h : checkRows rows = true) :
    ∀ row ∈ rows, 0 < eval row.coefficients (Real.log 2)⁻¹ ∧
      eval row.coefficients (Real.log 2)⁻¹ < 1 := by
  intro row hr
  exact checkCoefficient_sound (List.all_eq_true.mp h row hr)

end GeneralCK.Reflection.SmallBiasCoefficientBounds

end


