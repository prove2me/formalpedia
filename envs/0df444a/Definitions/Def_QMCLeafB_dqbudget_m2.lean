-- Prove2me | Definitions.Def_QMCLeafB_dqbudget_m2
-- name    : QMCLeafB_dqbudget_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:51:18.61342+00:00
-- url     : https://prove2.me/theorems/56e960e7-a3fb-4d21-9f38-51c663ceddde
-- title:
--   QMCLeafB dqbudget_m2
-- statement:
--   # leaf B phase 16 — `dqbudget` (swarm `smw1ez4a9`, member m2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_budget_bound_m1
import Definitions.Def_QMCLeafB_numcert_m6
import Definitions.Def_QMCLeafB_roundcount_estimate_m1
import Definitions.Def_QMCLeafB_fuelwire_m4
/-
# leaf B phase 16 — `dqbudget` (swarm `smw1ez4a9`, member m2)

**The round count at the campaign's own tolerance `dqShallow`.**

`FinalStroke.budgetRounds G dq m` is `Nat.clog 2 ⌈2Φ₀(dq)/r(dq)^(n·n)⌉₊ · m` with
`Φ₀(dq) = volPot (n·n) (initShapeOf (n·n) (2n²+2dq²)) = (√(2n²+2dq²))^(n²)` and
`r(dq) = dq/(8(Rq G+1))`.  m1's `BudgetBound.budgetRounds_le_log` is the `dq = 1` case; the campaign
needs `dq = dqShallow`, which is much smaller, so the radius contributes an extra `(1/dq)^(n²)`.

This file proves that the price of lowering the tolerance is **exactly `n²·log₂(1/dq)`**:

* `key_le` — `2Φ₀(dq)/r(dq)^N ≤ (2Φ₀(1)/r(1)^N)·(1/dq)^N` for `0 < dq ≤ 1` (both sides are
  `2Φ₀·(8(Rq+1)/dq)^N`, and `Φ₀` is increasing in `dq`);
* `clog_le` — hence `clog (dq) ≤ clog (dq = 1) + N·T` whenever `1/dq ≤ 2^T`;
* `budgetRounds_le_one_add` — `budgetRounds G dq m ≤ m·((n²+1)(clog 2 (⌈Rq⌉+1)+n+8) + n²·T)`;
* `budgetRounds_le_dqShallow` — at `dq = dqShallow G`, `T ≤ L+21` with `L` the encoded request's
  length (m6's `NumCert.clog_inv_dqShallow_le`), so
  `budgetRounds G dqShallow m ≤ m·((n+1)²·(bitCost (Rq G) + n + L + 40))`.

No `sorry`, no `axiom`; audits at the end.
-/

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.DqBudget

open QuantumMaxCutEnergy

/-- The campaign's starting volume potential at tolerance `dq`. -/
noncomputable def Phi (G : QuantumMaxCutEnergy.Input) (dq : ℚ) : ℝ :=
  QMCLeafB.EngineIterates.volPot (G.n * G.n)
    (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2))

/-- The engine's contraction radius at tolerance `dq`. -/
noncomputable def rate (G : QuantumMaxCutEnergy.Input) (dq : ℚ) : ℝ :=
  ((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))

theorem rate_pos (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (hdq : 0 < dq) : 0 < rate G dq := by
  unfold rate
  have h0 : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by
    have h := QMCLeafB.EngineRuntime.Rq_nonneg G
    exact_mod_cast h
  positivity

/-- The round count is the `clog` of `2Φ₀/r^N`. -/
theorem budgetRounds_def (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G dq m
      = Nat.clog 2 (Nat.ceil (2 * Phi G dq / (rate G dq) ^ (G.n * G.n))) * m := rfl

/-- `Φ₀` in closed form. -/
theorem Phi_eq (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (hdq : 0 < dq) :
    Phi G dq
      = Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ)) ^ (G.n * G.n) :=
  QMCLeafB.Boundary.volPot_initShapeOf (G.n * G.n) (by positivity)

/-- The potential is positive. -/
theorem Phi_pos (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (hdq : 0 < dq) : 0 < Phi G dq := by
  rw [Phi_eq G hdq]
  exact pow_pos (Real.sqrt_pos.2 (by positivity)) _

/-- **The potential grows with the tolerance.** -/
theorem Phi_mono (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (hdq : 0 < dq) (hdq1 : dq ≤ 1) :
    Phi G dq ≤ Phi G 1 := by
  have h1 : (0 : ℚ) < 1 := by norm_num
  rw [Phi_eq G hdq, Phi_eq G h1]
  have hb : ((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ)
      ≤ ((2 * (G.n : ℚ) ^ 2 + 2 * (1 : ℚ) ^ 2 : ℚ) : ℝ) := by
    have hsq : dq ^ 2 ≤ 1 := by nlinarith
    have : (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) ≤ 2 * (G.n : ℚ) ^ 2 + 2 * (1 : ℚ) ^ 2 := by
      nlinarith
    exact_mod_cast this
  exact pow_le_pow_left₀ (by positivity) (Real.sqrt_le_sqrt hb) _

/-- **The price of the tolerance, before the logarithm**: `1/r(dq) = (1/dq)·(1/r(1))`, so the whole
extra cost of the smaller tolerance is the factor `(1/dq)^N` in front of the `dq = 1` expression. -/
theorem key_le (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (hdq : 0 < dq) (hdq1 : dq ≤ 1) :
    2 * Phi G dq / (rate G dq) ^ (G.n * G.n)
      ≤ 2 * Phi G 1 / (rate G 1) ^ (G.n * G.n) * ((dq : ℝ)⁻¹) ^ (G.n * G.n) := by
  have hc : (0 : ℝ) < 8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) := by
    have h0 : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by
      have h := QMCLeafB.EngineRuntime.Rq_nonneg G
      exact_mod_cast h
    linarith
  have hdqR : (0 : ℝ) < (dq : ℝ) := by exact_mod_cast hdq
  have hinv : (rate G dq)⁻¹ = ((dq : ℝ)⁻¹) * (rate G 1)⁻¹ := by
    unfold rate
    rw [inv_div, inv_div]
    field_simp
    ring
  have hr : (0 : ℝ) < rate G 1 := rate_pos G (by norm_num : (0 : ℚ) < 1)
  calc 2 * Phi G dq / (rate G dq) ^ (G.n * G.n)
      = 2 * Phi G dq
          * (((dq : ℝ)⁻¹) ^ (G.n * G.n) * ((rate G 1)⁻¹) ^ (G.n * G.n)) := by
        rw [div_eq_mul_inv, ← inv_pow, hinv, mul_pow]
    _ ≤ 2 * Phi G 1
          * (((dq : ℝ)⁻¹) ^ (G.n * G.n) * ((rate G 1)⁻¹) ^ (G.n * G.n)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        linarith [Phi_mono G hdq hdq1]
    _ = 2 * Phi G 1 / (rate G 1) ^ (G.n * G.n) * ((dq : ℝ)⁻¹) ^ (G.n * G.n) := by
        rw [div_eq_mul_inv, inv_pow]
        ring

/-- **The logarithm's price**: `clog` at `dq` is `clog` at `1` plus `N·T` when `1/dq ≤ 2^T`. -/
theorem clog_le (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (hdq : 0 < dq) (hdq1 : dq ≤ 1)
    (T : ℕ) (hT : ((dq : ℝ)⁻¹) ≤ 2 ^ T) :
    Nat.clog 2 (Nat.ceil (2 * Phi G dq / (rate G dq) ^ (G.n * G.n)))
      ≤ Nat.clog 2 (Nat.ceil (2 * Phi G 1 / (rate G 1) ^ (G.n * G.n)))
        + (G.n * G.n) * T := by
  have hr1 : (0 : ℝ) < rate G 1 := rate_pos G (by norm_num : (0 : ℚ) < 1)
  have hN : (0 : ℝ) < 2 ^ ((G.n * G.n) * T) := by positivity
  have hpow : ((dq : ℝ)⁻¹) ^ (G.n * G.n) ≤ 2 ^ ((G.n * G.n) * T) := by
    have h1 : ((dq : ℝ)⁻¹) ^ (G.n * G.n) ≤ ((2 : ℝ) ^ T) ^ (G.n * G.n) :=
      pow_le_pow_left₀ (by positivity) hT _
    calc ((dq : ℝ)⁻¹) ^ (G.n * G.n) ≤ ((2 : ℝ) ^ T) ^ (G.n * G.n) := h1
      _ = 2 ^ ((G.n * G.n) * T) := by rw [← pow_mul]; ring_nf
  have hstep : 2 * Phi G dq / (rate G dq) ^ (G.n * G.n)
      ≤ 2 * Phi G 1 / (rate G 1) ^ (G.n * G.n) * 2 ^ ((G.n * G.n) * T) := by
    refine le_trans (key_le G hdq hdq1) ?_
    have hp : (0 : ℝ) < Phi G 1 := Phi_pos G (by norm_num : (0 : ℚ) < 1)
    have hden : (0 : ℝ) < (rate G 1) ^ (G.n * G.n) := pow_pos hr1 _
    exact mul_le_mul_of_nonneg_left hpow (le_of_lt (div_pos (by linarith) hden))
  have hceil : Nat.ceil (2 * Phi G dq / (rate G dq) ^ (G.n * G.n))
      ≤ Nat.ceil (2 * Phi G 1 / (rate G 1) ^ (G.n * G.n)) * 2 ^ ((G.n * G.n) * T) := by
    refine Nat.ceil_le.mpr ?_
    refine le_trans hstep ?_
    have hle : 2 * Phi G 1 / (rate G 1) ^ (G.n * G.n)
        ≤ ((Nat.ceil (2 * Phi G 1 / (rate G 1) ^ (G.n * G.n)) : ℕ) : ℝ) := Nat.le_ceil _
    have hcast : ((Nat.ceil (2 * Phi G 1 / (rate G 1) ^ (G.n * G.n)) * 2 ^ ((G.n * G.n) * T) : ℕ) : ℝ)
        = ((Nat.ceil (2 * Phi G 1 / (rate G 1) ^ (G.n * G.n)) : ℕ) : ℝ)
            * 2 ^ ((G.n * G.n) * T) := by push_cast; ring
    rw [hcast]
    exact mul_le_mul_of_nonneg_right hle hN.le
  have hpos1 : 1 ≤ Nat.ceil (2 * Phi G 1 / (rate G 1) ^ (G.n * G.n)) := by
    refine Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr ?_).ne'
    have hp := Phi_pos G (by norm_num : (0 : ℚ) < 1)
    have hden : (0 : ℝ) < (rate G 1) ^ (G.n * G.n) := pow_pos hr1 _
    exact div_pos (by linarith) hden
  have hpos2 : 1 ≤ 2 ^ ((G.n * G.n) * T) := Nat.one_le_two_pow
  calc Nat.clog 2 (Nat.ceil (2 * Phi G dq / (rate G dq) ^ (G.n * G.n)))
      ≤ Nat.clog 2 (Nat.ceil (2 * Phi G 1 / (rate G 1) ^ (G.n * G.n)) * 2 ^ ((G.n * G.n) * T)) :=
        Nat.clog_mono (by norm_num) le_rfl hceil
    _ ≤ Nat.clog 2 (Nat.ceil (2 * Phi G 1 / (rate G 1) ^ (G.n * G.n)))
          + Nat.clog 2 (2 ^ ((G.n * G.n) * T)) :=
        QMCLeafB.BudgetBound.clog_two_mul_le hpos1 hpos2
    _ = Nat.clog 2 (Nat.ceil (2 * Phi G 1 / (rate G 1) ^ (G.n * G.n)))
          + (G.n * G.n) * T := by rw [Nat.clog_pow 2 ((G.n * G.n) * T) (by norm_num)]

/-! ## 5.  The round count at an arbitrary tolerance `dq ≤ 1` -/

/-- **`budgetRounds` at `dq ≤ 1`, priced by `log₂(1/dq)`.** -/
theorem budgetRounds_le_one_add (G : QuantumMaxCutEnergy.Input) (m : ℕ) {dq : ℚ}
    (hdq : 0 < dq) (hdq1 : dq ≤ 1) (T : ℕ) (hT : ((dq : ℝ)⁻¹) ≤ 2 ^ T) :
    QMCLeafB.FinalStroke.budgetRounds G dq m
      ≤ m * ((G.n * G.n + 1)
          * (Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n + 8)
          + (G.n * G.n) * T) := by
  have hA : Nat.clog 2 (Nat.ceil (2 * Phi G 1 / (rate G 1) ^ (G.n * G.n)))
      ≤ (G.n * G.n + 1)
          * (Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n + 8) := by
    have h := QMCLeafB.BudgetBound.budgetRounds_le_log G 1
    rw [budgetRounds_def] at h
    simpa using h
  calc QMCLeafB.FinalStroke.budgetRounds G dq m
      = Nat.clog 2 (Nat.ceil (2 * Phi G dq / (rate G dq) ^ (G.n * G.n))) * m := budgetRounds_def G dq m
    _ ≤ (Nat.clog 2 (Nat.ceil (2 * Phi G 1 / (rate G 1) ^ (G.n * G.n))) + (G.n * G.n) * T) * m :=
        Nat.mul_le_mul_right m (clog_le G hdq hdq1 T hT)
    _ ≤ ((G.n * G.n + 1)
          * (Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n + 8)
            + (G.n * G.n) * T) * m :=
        Nat.mul_le_mul_right m (Nat.add_le_add_right hA _)
    _ = m * ((G.n * G.n + 1)
          * (Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n + 8)
            + (G.n * G.n) * T) := by ring

/-! ## 6.  The campaign's tolerance -/

/-- **The round count at `dqShallow`.**  The tolerance's own `clog` is at most the encoded request's
length plus 21 (m6's `NumCert.clog_inv_dqShallow_le`), so the count is a cubic in `(n, bitCost, L)`. -/
theorem budgetRounds_le_dqShallow (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G) m
      ≤ m * ((G.n + 1) ^ 2
          * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G)
            + (QuantumMaxCutEnergy.encodeInput G).length + G.n + 40)) := by
  have hdq : (0 : ℚ) < QMCLeafB.RundataParams.dqShallow G :=
    QMCLeafB.RundataParams.dqShallow_pos G
  have hdq1 : QMCLeafB.RundataParams.dqShallow G ≤ 1 := QMCLeafB.NumCert.dqShallow_le_one G
  set T := Nat.clog 2 (Nat.ceil (1 / QMCLeafB.RundataParams.dqShallow G) + 1) with hTdef
  have hTq : (1 / QMCLeafB.RundataParams.dqShallow G : ℚ) ≤ (2 : ℚ) ^ T := by
    have hle : Nat.ceil (1 / QMCLeafB.RundataParams.dqShallow G) ≤ 2 ^ T := by
      calc Nat.ceil (1 / QMCLeafB.RundataParams.dqShallow G)
          ≤ Nat.ceil (1 / QMCLeafB.RundataParams.dqShallow G) + 1 := Nat.le_succ _
        _ ≤ 2 ^ T := Nat.le_pow_clog (by norm_num) _
    calc (1 / QMCLeafB.RundataParams.dqShallow G : ℚ)
        ≤ (Nat.ceil (1 / QMCLeafB.RundataParams.dqShallow G) : ℚ) := Nat.le_ceil _
      _ ≤ ((2 ^ T : ℕ) : ℚ) := by exact_mod_cast hle
      _ = (2 : ℚ) ^ T := by push_cast; ring
  have hT : (((QMCLeafB.RundataParams.dqShallow G : ℚ)) : ℝ)⁻¹ ≤ (2 : ℝ) ^ T := by
    have h1 : ((1 / QMCLeafB.RundataParams.dqShallow G : ℚ) : ℝ) ≤ ((2 : ℚ) ^ T : ℝ) := by
      exact_mod_cast hTq
    have h2 : ((1 / QMCLeafB.RundataParams.dqShallow G : ℚ) : ℝ)
        = (((QMCLeafB.RundataParams.dqShallow G : ℚ)) : ℝ)⁻¹ := by
      push_cast
      ring
    have h3 : ((2 : ℚ) ^ T : ℝ) = (2 : ℝ) ^ T := by push_cast; ring
    rwa [h2, h3] at h1
  have hTL : T ≤ (QuantumMaxCutEnergy.encodeInput G).length + 21 := by
    rw [hTdef]
    exact QMCLeafB.NumCert.clog_inv_dqShallow_le G hRq
  have hbc : Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1)
      ≤ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1 :=
    QMCLeafB.RoundCountEstimate.clog_ceil_Rq_le G
  have hmain := budgetRounds_le_one_add G m hdq hdq1 T hT
  refine le_trans hmain ?_
  apply Nat.mul_le_mul_left
  have hsq : G.n * G.n ≤ (G.n + 1) ^ 2 := by nlinarith
  have hs1 : G.n * G.n + 1 ≤ (G.n + 1) ^ 2 := by nlinarith
  calc (G.n * G.n + 1)
        * (Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n + 8)
          + (G.n * G.n) * T
      ≤ (G.n + 1) ^ 2
          * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1 + G.n + 8)
            + (G.n + 1) ^ 2 * ((QuantumMaxCutEnergy.encodeInput G).length + 21) := by
        refine Nat.add_le_add (Nat.mul_le_mul hs1 (by omega)) ?_
        exact Nat.mul_le_mul hsq hTL
    _ = (G.n + 1) ^ 2
          * ((QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1 + G.n + 8)
            + ((QuantumMaxCutEnergy.encodeInput G).length + 21)) := by ring
    _ ≤ (G.n + 1) ^ 2
          * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G)
            + (QuantumMaxCutEnergy.encodeInput G).length + G.n + 40) := by
        apply Nat.mul_le_mul_left
        omega

/-! ## 7.  The tolerance in `bitCost` form -/

/-- **`1 ≤ 2^(bitCost q) · q`**: the bit cost bounds the magnitude of a rational from below as well
as from above.  This is what turns `1/dqShallow ≈ 3.6·10⁶/Rq` into a power of two. -/
theorem one_le_two_pow_bitCost_mul (q : ℚ) (hq : 0 < q) :
    1 ≤ (2 : ℚ) ^ QMCLeafB.Hspec.bitCost q * q := by
  have hden : (0 : ℕ) < q.den := q.den_pos
  have hqeq : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
  have hdenQ : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast hden
  have hq' : (0 : ℚ) < (q.num : ℚ) / (q.den : ℚ) := by rw [← hqeq]; exact hq
  have hnumQ : (0 : ℚ) < (q.num : ℚ) := by
    rcases div_pos_iff.mp hq' with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd h2 (not_lt.mpr hdenQ.le)
  have hnum_int : (0 : ℤ) < q.num := by exact_mod_cast hnumQ
  have hnumPos : 0 < q.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hnum_int)
  have hnum_ge : 2 ^ (Nat.size q.num.natAbs - 1) ≤ q.num.natAbs :=
    Nat.lt_size.mp (by have := Nat.size_pos.mpr hnumPos; omega)
  have hden_lt : q.den < 2 ^ Nat.size q.den := Nat.size_le.mp le_rfl
  have hnum_eq : (q.num.natAbs : ℚ) = (q.num : ℚ) := by
    have h : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg hnum_int.le
    calc (q.num.natAbs : ℚ) = ((q.num.natAbs : ℤ) : ℚ) := by rw [Int.cast_natCast]
      _ = (q.num : ℚ) := by rw [h]
  have h1 : (2 : ℚ) ^ (Nat.size q.num.natAbs - 1) ≤ (q.num : ℚ) := by
    have h2 : ((2 ^ (Nat.size q.num.natAbs - 1) : ℕ) : ℚ) ≤ (q.num.natAbs : ℚ) := by
      exact_mod_cast hnum_ge
    have h3 : ((2 ^ (Nat.size q.num.natAbs - 1) : ℕ) : ℚ)
        = (2 : ℚ) ^ (Nat.size q.num.natAbs - 1) := by push_cast; ring
    rw [h3, hnum_eq] at h2
    exact h2
  have h2 : ((q.den : ℕ) : ℚ) < (2 : ℚ) ^ Nat.size q.den := by exact_mod_cast hden_lt
  have hstep : (2 : ℚ) ^ (Nat.size q.num.natAbs - 1) ≤ q * (2 : ℚ) ^ Nat.size q.den := by
    have hkey : (q.num : ℚ) ≤ q * (2 : ℚ) ^ Nat.size q.den := by
      have hqden : q * (q.den : ℚ) = (q.num : ℚ) := Rat.mul_den_eq_num q
      calc (q.num : ℚ) = q * (q.den : ℚ) := hqden.symm
        _ ≤ q * (2 : ℚ) ^ Nat.size q.den :=
            mul_le_mul_of_nonneg_left h2.le hq.le
    linarith
  have h2a : (2 : ℚ) ^ QMCLeafB.Hspec.bitCost q * q
      = (2 : ℚ) ^ (Nat.size q.num.natAbs + 1) * ((2 : ℚ) ^ Nat.size q.den * q) := by
    unfold QMCLeafB.Hspec.bitCost
    rw [pow_add, pow_add]
    ring
  rw [h2a]
  have h3 : (1 : ℚ) ≤ (2 : ℚ) ^ (Nat.size q.num.natAbs + 1)
      * (2 : ℚ) ^ (Nat.size q.num.natAbs - 1) := by
    rw [← pow_add]
    have hexp : Nat.size q.num.natAbs + 1 + (Nat.size q.num.natAbs - 1)
        = 2 * Nat.size q.num.natAbs := by
      have := Nat.size_pos.mpr hnumPos
      omega
    rw [hexp]
    exact one_le_pow₀ (by norm_num : (1:ℚ) ≤ 2)
  have h4 : (0 : ℚ) < (2 : ℚ) ^ (Nat.size q.num.natAbs + 1) := by positivity
  have h5 : (2 : ℚ) ^ (Nat.size q.num.natAbs - 1)
      ≤ (2 : ℚ) ^ Nat.size q.den * q := by
    rw [mul_comm]
    exact hstep
  calc (1 : ℚ) ≤ (2 : ℚ) ^ (Nat.size q.num.natAbs + 1)
        * (2 : ℚ) ^ (Nat.size q.num.natAbs - 1) := h3
    _ ≤ (2 : ℚ) ^ (Nat.size q.num.natAbs + 1) * ((2 : ℚ) ^ Nat.size q.den * q) :=
        mul_le_mul_of_nonneg_left h5 h4.le

/-- **The shallow tolerance in `bitCost` form**: `1/dqShallow ≤ 2^(bitCost (Rq G) + 20)`. -/
theorem inv_dqShallow_le_bitCost (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    (1 : ℚ) / QMCLeafB.RundataParams.dqShallow G
      ≤ (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 20) := by
  have hne : QMCLeafB.EngineRuntime.Rq G ≠ 0 := hRq.ne'
  rw [QMCLeafB.NumCert.dqShallow_eq_core G hne, QMCLeafB.NumCert.dqShallowCore_eq G]
  have key : (1 : ℚ) / (QMCLeafB.EngineRuntime.Rq G
        / (40000 * (9 * QMCLeafB.EngineRuntime.Rq G + 1)))
      = 360000 + 40000 * (1 / QMCLeafB.EngineRuntime.Rq G) := by
    field_simp
    ring
  rw [key]
  have hbc : 1 / QMCLeafB.EngineRuntime.Rq G
      ≤ (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G)) := by
    have h := one_le_two_pow_bitCost_mul (QMCLeafB.EngineRuntime.Rq G) hRq
    rw [div_le_iff₀ hRq]
    linarith
  have hpow : (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 20)
      = (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G)) * 1048576 := by
    rw [pow_add]
    norm_num
  rw [hpow]
  have h1 : (1 : ℚ) ≤ (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G)) :=
    one_le_pow₀ (by norm_num : (1:ℚ) ≤ 2)
  nlinarith [hbc, h1]

/-- **`clog 2 (⌈1/dqShallow⌉ + 1) ≤ bitCost + 21`.** -/
theorem clog_inv_dqShallow_le_bitCost (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    Nat.clog 2 (Nat.ceil (1 / QMCLeafB.RundataParams.dqShallow G) + 1)
      ≤ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 21 := by
  refine (Nat.clog_le_iff_le_pow (by norm_num)).mpr ?_
  have h1 := inv_dqShallow_le_bitCost G hRq
  have hcast : ((2 : ℚ) ^ (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 20))
      = ((2 ^ (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 20) : ℕ) : ℚ) := by
    push_cast
    ring
  have h2 : Nat.ceil (1 / QMCLeafB.RundataParams.dqShallow G)
      ≤ 2 ^ (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 20) :=
    Nat.ceil_le.mpr (hcast ▸ h1)
  have h3 : Nat.ceil (1 / QMCLeafB.RundataParams.dqShallow G) + 1
      ≤ 2 ^ (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 20)
        + 2 ^ (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 20) := by
    have h4 : (1 : ℕ) ≤ 2 ^ (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 20) :=
      Nat.one_le_two_pow
    omega
  refine le_trans h3 (le_of_eq ?_)
  rw [show QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 21
      = (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 20) + 1 by omega, pow_succ]
  ring

/-- **The round count at `dqShallow`, in `bitCost` form.** -/
theorem budgetRounds_le_dqShallow_bitCost (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G) m
      ≤ m * ((G.n + 1) ^ 2
          * (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 30)) := by
  have hdq : (0 : ℚ) < QMCLeafB.RundataParams.dqShallow G :=
    QMCLeafB.RundataParams.dqShallow_pos G
  have hdq1 : QMCLeafB.RundataParams.dqShallow G ≤ 1 := QMCLeafB.NumCert.dqShallow_le_one G
  set T := Nat.clog 2 (Nat.ceil (1 / QMCLeafB.RundataParams.dqShallow G) + 1) with hTdef
  have hTq : (1 / QMCLeafB.RundataParams.dqShallow G : ℚ) ≤ (2 : ℚ) ^ T := by
    have hle : Nat.ceil (1 / QMCLeafB.RundataParams.dqShallow G) ≤ 2 ^ T := by
      calc Nat.ceil (1 / QMCLeafB.RundataParams.dqShallow G)
          ≤ Nat.ceil (1 / QMCLeafB.RundataParams.dqShallow G) + 1 := Nat.le_succ _
        _ ≤ 2 ^ T := Nat.le_pow_clog (by norm_num) _
    calc (1 / QMCLeafB.RundataParams.dqShallow G : ℚ)
        ≤ (Nat.ceil (1 / QMCLeafB.RundataParams.dqShallow G) : ℚ) := Nat.le_ceil _
      _ ≤ ((2 ^ T : ℕ) : ℚ) := by exact_mod_cast hle
      _ = (2 : ℚ) ^ T := by push_cast; ring
  have hT : (((QMCLeafB.RundataParams.dqShallow G : ℚ)) : ℝ)⁻¹ ≤ (2 : ℝ) ^ T := by
    have h1 : ((1 / QMCLeafB.RundataParams.dqShallow G : ℚ) : ℝ) ≤ ((2 : ℚ) ^ T : ℝ) := by
      exact_mod_cast hTq
    have h2 : ((1 / QMCLeafB.RundataParams.dqShallow G : ℚ) : ℝ)
        = (((QMCLeafB.RundataParams.dqShallow G : ℚ)) : ℝ)⁻¹ := by
      push_cast
      ring
    have h3 : ((2 : ℚ) ^ T : ℝ) = (2 : ℝ) ^ T := by push_cast; ring
    rwa [h2, h3] at h1
  have hTL : T ≤ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 21 := by
    rw [hTdef]
    exact clog_inv_dqShallow_le_bitCost G hRq
  have hbc : Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1)
      ≤ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1 :=
    QMCLeafB.RoundCountEstimate.clog_ceil_Rq_le G
  have hmain := budgetRounds_le_one_add G m hdq hdq1 T hT
  refine le_trans hmain ?_
  apply Nat.mul_le_mul_left
  have hsq : G.n * G.n ≤ (G.n + 1) ^ 2 := by nlinarith
  have hs1 : G.n * G.n + 1 ≤ (G.n + 1) ^ 2 := by nlinarith
  calc (G.n * G.n + 1)
        * (Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n + 8)
          + (G.n * G.n) * T
      ≤ (G.n + 1) ^ 2
          * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1 + G.n + 8)
            + (G.n + 1) ^ 2 * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 21) := by
        refine Nat.add_le_add (Nat.mul_le_mul hs1 (by omega)) ?_
        exact Nat.mul_le_mul hsq hTL
    _ = (G.n + 1) ^ 2
          * ((QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1 + G.n + 8)
            + (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 21)) := by ring
    _ ≤ (G.n + 1) ^ 2
          * (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 30) := by
        apply Nat.mul_le_mul_left
        omega

/-- **The round count at `dqShallow` is under four copies of m4's `Kbc`** — the shape the fuel
program computes (`FuelWire.poly_Kbc_mHalve_mul`). -/
theorem budgetRounds_le_Kbc4 (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G) m
      ≤ 4 * QMCLeafB.FuelWire.Kbc m G := by
  refine le_trans (budgetRounds_le_dqShallow_bitCost G hRq m) ?_
  rw [QMCLeafB.FuelWire.Kbc_eq]
  have hinner : 2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 30
      ≤ 4 * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 10) := by omega
  calc m * ((G.n + 1) ^ 2
        * (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 30))
      ≤ m * ((G.n + 1) ^ 2
        * (4 * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 10))) := by
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul_left _ hinner
    _ = 4 * (m * ((G.n + 1) ^ 2
        * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 10))) := by ring

end QMCLeafB.DqBudget

#print axioms QMCLeafB.DqBudget.Phi_eq
#print axioms QMCLeafB.DqBudget.Phi_mono
#print axioms QMCLeafB.DqBudget.key_le
#print axioms QMCLeafB.DqBudget.clog_le
#print axioms QMCLeafB.DqBudget.budgetRounds_le_one_add
#print axioms QMCLeafB.DqBudget.budgetRounds_le_dqShallow
#print axioms QMCLeafB.DqBudget.one_le_two_pow_bitCost_mul
#print axioms QMCLeafB.DqBudget.inv_dqShallow_le_bitCost
#print axioms QMCLeafB.DqBudget.clog_inv_dqShallow_le_bitCost
#print axioms QMCLeafB.DqBudget.budgetRounds_le_dqShallow_bitCost
#print axioms QMCLeafB.DqBudget.budgetRounds_le_Kbc4


