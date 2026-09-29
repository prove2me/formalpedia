-- Prove2me | Definitions.Def_CK_CKLaneE_FastLog
-- name    : CK_CKLaneE_FastLog
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:50:36.040459+00:00
-- url     : https://prove2.me/theorems/8b97b606-d34d-4a3a-8cea-1ace8948bdc0
-- title:
--   Courtade–Kumar proof module `CKLaneE.FastLog` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.FastLog` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.FastLog` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.FastLog (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/FastLog.lean)

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

-- ===== source module CKLaneE.FastLog =====
section

/-!
# Lane E: fast natural-number atanh series for `log`, kernel-checkable

For `x = u/v` with `u < v`, the atanh series gives
`Σ_{k<n} x^(2k+1)/(2k+1) ≤ ½ log((1+x)/(1-x)) ≤ Σ_{k<n} x^(2k+1)/(2k+1) + x^(2n+1)/(1-x²)`
(Mathlib `Real.sum_range_le_log_div`, `Real.log_div_le_sum_range_add`).  The partial sums are
computed in fixed point `T = 2^48` with floor (lower) / ceiling (upper) division, using only `ℕ`
multiplication and division (GMP-accelerated in the kernel).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.FL

def T : ℕ := 2 ^ 48

theorem T_pos : 0 < T := by unfold T; positivity

/-- Ceiling division. -/
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

theorem le_cdiv_mul (a : ℕ) {b : ℕ} (hb : 0 < b) : a ≤ cdiv a b * b := by
  unfold cdiv
  have h := Nat.div_add_mod (a + b - 1) b
  have hm := Nat.mod_lt (a + b - 1) hb
  have : b * ((a + b - 1) / b) = (a + b - 1) - (a + b - 1) % b := by omega
  rw [mul_comm]
  omega

theorem div_le_cdiv_real (a : ℕ) {b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ (cdiv a b : ℝ) := by
  have h := le_cdiv_mul a hb
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  exact_mod_cast h

theorem fdiv_le_real (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := Nat.cast_div_le

/-- Lower state: (floor partial sum, floor power `≈ T x^(2n+1)`). -/
def stLo (u v : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, T * u / v)
  | n + 1 =>
      let p := stLo u v n
      (p.1 + p.2 / (2 * n + 1), p.2 * (u * u) / (v * v))

/-- Upper state: (ceiling partial sum, ceiling power). -/
def stHi (u v : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, cdiv (T * u) v)
  | n + 1 =>
      let p := stHi u v n
      (p.1 + cdiv p.2 (2 * n + 1), cdiv (p.2 * (u * u)) (v * v))

theorem stLo_spec (u v : ℕ) (hv : 0 < v) (n : ℕ) :
    ((stLo u v n).1 : ℝ) ≤ T * ∑ k ∈ Finset.range n, ((u : ℝ) / v) ^ (2 * k + 1) / (2 * k + 1) ∧
      ((stLo u v n).2 : ℝ) ≤ T * ((u : ℝ) / v) ^ (2 * n + 1) := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hx0 : (0 : ℝ) ≤ (u : ℝ) / v := by positivity
  induction n with
  | zero =>
    simp only [stLo, Finset.range_zero, Finset.sum_empty, mul_zero, Nat.cast_zero, le_refl,
      true_and]
    rw [show (0 : ℕ) + 1 = 1 from rfl, pow_one]
    have h := fdiv_le_real (T * u) v
    push_cast at h
    calc (((T * u / v : ℕ)) : ℝ) ≤ (T : ℝ) * u / v := h
      _ = T * ((u : ℝ) / v) := by ring
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [stLo]
    constructor
    · rw [Finset.sum_range_succ]
      push_cast
      have h := fdiv_le_real (stLo u v n).2 (2 * n + 1)
      push_cast at h
      have hd : (0 : ℝ) < 2 * n + 1 := by positivity
      have h2 : ((stLo u v n).2 : ℝ) / (2 * n + 1) ≤ T * ((u : ℝ) / v) ^ (2 * n + 1) / (2 * n + 1) :=
        div_le_div_of_nonneg_right ih2 hd.le
      have e : (T : ℝ) * (∑ k ∈ Finset.range n, ((u : ℝ) / v) ^ (2 * k + 1) / (2 * k + 1) +
          ((u : ℝ) / v) ^ (2 * n + 1) / (2 * n + 1)) =
          T * ∑ k ∈ Finset.range n, ((u : ℝ) / v) ^ (2 * k + 1) / (2 * k + 1) +
            T * ((u : ℝ) / v) ^ (2 * n + 1) / (2 * n + 1) := by ring
      rw [e]
      linarith
    · have h := fdiv_le_real ((stLo u v n).2 * (u * u)) (v * v)
      push_cast at h
      have hvv : (0 : ℝ) < (v : ℝ) * v := by positivity
      have h2 : ((stLo u v n).2 : ℝ) * ((u : ℝ) * u) / ((v : ℝ) * v) ≤
          T * ((u : ℝ) / v) ^ (2 * n + 1) * ((u : ℝ) * u) / ((v : ℝ) * v) := by
        apply div_le_div_of_nonneg_right _ hvv.le
        exact mul_le_mul_of_nonneg_right ih2 (by positivity)
      have e : (T : ℝ) * ((u : ℝ) / v) ^ (2 * n + 1) * ((u : ℝ) * u) / ((v : ℝ) * v) =
          T * ((u : ℝ) / v) ^ (2 * (n + 1) + 1) := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add, div_pow]
        ring
      linarith

theorem stHi_spec (u v : ℕ) (hv : 0 < v) (n : ℕ) :
    T * ∑ k ∈ Finset.range n, ((u : ℝ) / v) ^ (2 * k + 1) / (2 * k + 1) ≤ ((stHi u v n).1 : ℝ) ∧
      T * ((u : ℝ) / v) ^ (2 * n + 1) ≤ ((stHi u v n).2 : ℝ) := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  induction n with
  | zero =>
    simp only [stHi, Finset.range_zero, Finset.sum_empty, mul_zero, Nat.cast_zero, le_refl,
      true_and]
    rw [show (0 : ℕ) + 1 = 1 from rfl, pow_one]
    have h := div_le_cdiv_real (T * u) hv
    push_cast at h
    calc (T : ℝ) * ((u : ℝ) / v) = (T : ℝ) * u / v := by ring
      _ ≤ _ := h
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [stHi]
    constructor
    · rw [Finset.sum_range_succ]
      push_cast
      have hd : 0 < 2 * n + 1 := by omega
      have h := div_le_cdiv_real (stHi u v n).2 hd
      push_cast at h
      have hd' : (0 : ℝ) < 2 * n + 1 := by positivity
      have h2 : T * ((u : ℝ) / v) ^ (2 * n + 1) / (2 * n + 1) ≤ ((stHi u v n).2 : ℝ) / (2 * n + 1) :=
        div_le_div_of_nonneg_right ih2 hd'.le
      have e : (T : ℝ) * (∑ k ∈ Finset.range n, ((u : ℝ) / v) ^ (2 * k + 1) / (2 * k + 1) +
          ((u : ℝ) / v) ^ (2 * n + 1) / (2 * n + 1)) =
          T * ∑ k ∈ Finset.range n, ((u : ℝ) / v) ^ (2 * k + 1) / (2 * k + 1) +
            T * ((u : ℝ) / v) ^ (2 * n + 1) / (2 * n + 1) := by ring
      rw [e]
      linarith
    · have hvv : 0 < v * v := Nat.mul_pos hv hv
      have h := div_le_cdiv_real ((stHi u v n).2 * (u * u)) hvv
      push_cast at h
      have hvv' : (0 : ℝ) < (v : ℝ) * v := by positivity
      have h2 : T * ((u : ℝ) / v) ^ (2 * n + 1) * ((u : ℝ) * u) / ((v : ℝ) * v) ≤
          ((stHi u v n).2 : ℝ) * ((u : ℝ) * u) / ((v : ℝ) * v) := by
        apply div_le_div_of_nonneg_right _ hvv'.le
        exact mul_le_mul_of_nonneg_right ih2 (by positivity)
      have e : (T : ℝ) * ((u : ℝ) / v) ^ (2 * n + 1) * ((u : ℝ) * u) / ((v : ℝ) * v) =
          T * ((u : ℝ) / v) ^ (2 * (n + 1) + 1) := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add, div_pow]
        ring
      linarith

/-- Fixed-point lower bound of `T * ½ log((1+x)/(1-x))`. -/
def serLo (u v n : ℕ) : ℕ := (stLo u v n).1

/-- Fixed-point upper bound of `T * ½ log((1+x)/(1-x))` (tail `x^(2n+1)/(1-x²)` included). -/
def serHi (u v n : ℕ) : ℕ := (stHi u v n).1 + cdiv ((stHi u v n).2 * (v * v)) (v * v - u * u)

theorem ser_bounds {u v : ℕ} (huv : u < v) (n : ℕ) :
    (serLo u v n : ℝ) / T ≤ 1 / 2 * Real.log ((1 + (u : ℝ) / v) / (1 - (u : ℝ) / v)) ∧
      1 / 2 * Real.log ((1 + (u : ℝ) / v) / (1 - (u : ℝ) / v)) ≤ (serHi u v n : ℝ) / T := by
  have hv : 0 < v := lt_of_le_of_lt (Nat.zero_le u) huv
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hT : (0 : ℝ) < T := by exact_mod_cast T_pos
  have huv' : (u : ℝ) < v := by exact_mod_cast huv
  set x : ℝ := (u : ℝ) / v with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := (div_lt_one hv').mpr huv'
  obtain ⟨l1, _⟩ := stLo_spec u v hv n
  obtain ⟨h1, h2⟩ := stHi_spec u v hv n
  have hlo := Real.sum_range_le_log_div hx0 hx1 n
  have hhi := Real.log_div_le_sum_range_add hx0 hx1 n
  constructor
  · rw [div_le_iff₀ hT]
    unfold serLo
    have := mul_le_mul_of_nonneg_left hlo hT.le
    linarith
  · unfold serHi
    have hvv : 0 < v * v - u * u := by
      have : u * u < v * v := Nat.mul_self_lt_mul_self huv
      omega
    have hc := div_le_cdiv_real ((stHi u v n).2 * (v * v)) hvv
    have hcast : ((v * v - u * u : ℕ) : ℝ) = (v : ℝ) * v - (u : ℝ) * u := by
      have : u * u ≤ v * v := (Nat.mul_self_lt_mul_self huv).le
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast] at hc
    push_cast at hc
    have hden : (0 : ℝ) < (v : ℝ) * v - (u : ℝ) * u := by nlinarith
    -- tail: x^(2n+1)/(1-x^2) = (x^(2n+1)) * v^2/(v^2-u^2)
    have htail : x ^ (2 * n + 1) / (1 - x ^ 2) =
        x ^ (2 * n + 1) * ((v : ℝ) * v) / ((v : ℝ) * v - (u : ℝ) * u) := by
      rw [hx]
      field_simp
    have ht2 : T * (x ^ (2 * n + 1) * ((v : ℝ) * v) / ((v : ℝ) * v - (u : ℝ) * u)) ≤
        ((stHi u v n).2 : ℝ) * ((v : ℝ) * v) / ((v : ℝ) * v - (u : ℝ) * u) := by
      rw [← mul_div_assoc, ← mul_assoc]
      apply div_le_div_of_nonneg_right _ hden.le
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    rw [le_div_iff₀ hT]
    push_cast
    have := mul_le_mul_of_nonneg_left hhi hT.le
    rw [htail] at this
    nlinarith

/-! ## `log 2` constant -/

def L2n : ℕ := 30

/-- `½ log 2 = ½ log((1+1/3)/(1-1/3))`, so `log 2 ∈ [2 serLo 1 3 L2n / T, 2 serHi 1 3 L2n / T]`. -/
theorem log_two_bounds :
    2 * (serLo 1 3 L2n : ℝ) / T ≤ Real.log 2 ∧ Real.log 2 ≤ 2 * (serHi 1 3 L2n : ℝ) / T := by
  have h := ser_bounds (u := 1) (v := 3) (by norm_num) L2n
  have e : (1 + ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) / (1 - ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = 2 := by
    norm_num
  rw [e] at h
  have hT : (0 : ℝ) < T := by exact_mod_cast T_pos
  obtain ⟨h1, h2⟩ := h
  constructor
  · rw [div_le_iff₀ hT]
    rw [div_le_iff₀ hT] at h1
    linarith
  · rw [le_div_iff₀ hT]
    rw [le_div_iff₀ hT] at h2
    linarith

end CKLaneE.FL

#check @CKLaneE.FL.ser_bounds
#check @CKLaneE.FL.log_two_bounds
#print axioms CKLaneE.FL.ser_bounds
#print axioms CKLaneE.FL.log_two_bounds

end


