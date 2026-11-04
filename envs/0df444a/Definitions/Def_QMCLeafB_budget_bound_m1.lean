-- Prove2me | Definitions.Def_QMCLeafB_budget_bound_m1
-- name    : QMCLeafB_budget_bound_m1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:38:57.06519+00:00
-- url     : https://prove2.me/theorems/4489acde-ad26-4fc9-b142-e1259924d717
-- title:
--   QMCLeafB budget_bound_m1
-- statement:
--   # leaf B phase 13 — `budget-bound` (swarm `smw17fqzz`, member m1, direction d6)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_final_stroke_m7
/-
# leaf B phase 13 — `budget-bound` (swarm `smw17fqzz`, member m1, direction d6)

**The round count, bounded.**  `FinalStroke.budgetRounds G dq m` is the `Nat.clog 2` expression the
fuel must dominate (`simRounds` at the campaign's radius).  m8's f47 records it as the last unproved
numeric statement, in the form `budgetRounds G dqV m ≤ (G.n + 1)^d` with `d` fixed — which is
**false**: `budgetRounds ≈ m·n²·(log2 Rq + O(log n))` and `Rq` is the input's total weight, whose
bit length is carried by the request, not by `n`.  This file proves the honest bound:

    budgetRounds G 1 m ≤ m * ((n² + 1) * (⌈Rq G⌉ + n + 8))

i.e. the run is at most cubic in `n` and **linear in the total weight**.  Two corollaries for the
fuel: since a rational's magnitude is bounded by `2` raised to its encoded length, this converts to a
monomial in the input length `L` (the missing step is `⌈Rq G⌉ ≤ 2^L`, which needs the `Ratio.encode`
size lemma); and the shape of the bound is what `monomial_mul_le_seed_pow` can absorb once the fuel
length is taken to be `(n+1)^d * (L+1)^e * m` rather than `(n+1)^d * m`.

Contents:
* `clog_two_le_self`, `clog_two_mul_le` — `clog 2 X ≤ X`, `clog 2 (xy) ≤ clog 2 x + clog 2 y`;
* `two_le_two_pow` — `2 ≤ 2^N`;
* `budgetRounds_le_clog` — `budgetRounds G 1 m ≤ m * ((n² + 1) * (Nat.clog 2 ⌈A⌉ + 2))` at
  `A = √(2n²+2)·8(Rq+1)`, the exact content of `Nat.clog` at the campaign's radius;
* `clog_baseA_le` — `Nat.clog 2 ⌈A⌉ ≤ ⌈Rq G⌉ + n + 6`;
* `budgetRounds_le_value` — the bound above.

No `sorry`, no `axiom`; audits at the end.
-/

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.BudgetBound

open QuantumMaxCutEnergy

/-! ## 1.  Elementary `Nat.clog` facts -/

/-- `X ≤ 2^X` for `X ≥ 1`. -/
theorem le_two_pow {X : ℕ} (hX : 1 ≤ X) : X ≤ 2 ^ X := by
  induction X with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; norm_num
      · have h1 : k ≤ 2 ^ k := ih (by omega)
        have h2 : (k + 1) ≤ 2 * k := by omega
        have h3 : 2 * (2 : ℕ) ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
        calc k + 1 ≤ 2 * k := h2
          _ ≤ 2 * 2 ^ k := by omega
          _ = 2 ^ (k + 1) := h3

/-- **`clog 2 X ≤ X`** for `X ≥ 1` (the crude bound that is enough here). -/
theorem clog_two_le_self {X : ℕ} (hX : 1 ≤ X) : Nat.clog 2 X ≤ X :=
  (Nat.clog_le_iff_le_pow (by norm_num)).mpr (le_two_pow hX)

/-- `a + 1 ≤ 2^a`. -/
theorem succ_le_two_pow (a : ℕ) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => norm_num
  | succ k ih =>
      have h1 : k + 1 + 1 ≤ 2 ^ k + 2 ^ k := by
        have : (k + 1) ≤ 2 ^ k := ih
        omega
      have h2 : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
      omega

/-- **`Nat.clog 2 (a+1) ≤ a`** — the successor costs no bit. -/
theorem clog_succ_le (a : ℕ) : Nat.clog 2 (a + 1) ≤ a :=
  (Nat.clog_le_iff_le_pow (by norm_num)).mpr (succ_le_two_pow a)

/-- **`clog` of a product is at most the sum.** -/
theorem clog_two_mul_le {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    Nat.clog 2 (x * y) ≤ Nat.clog 2 x + Nat.clog 2 y := by
  refine (Nat.clog_le_iff_le_pow (by norm_num)).mpr ?_
  have h1 : x ≤ 2 ^ Nat.clog 2 x := Nat.le_pow_clog (by norm_num) x
  have h2 : y ≤ 2 ^ Nat.clog 2 y := Nat.le_pow_clog (by norm_num) y
  calc x * y ≤ 2 ^ Nat.clog 2 x * 2 ^ Nat.clog 2 y := Nat.mul_le_mul h1 h2
    _ = 2 ^ (Nat.clog 2 x + Nat.clog 2 y) := (pow_add _ _ _).symm

/-- `2 ≤ 2^N` for `N ≥ 1`. -/
theorem two_le_two_pow {N : ℕ} (hN : 1 ≤ N) : (2 : ℕ) ≤ 2 ^ N := by
  calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN

/-! ## 2.  The campaign's radius and starting potential, at `dq = 1` -/

/-- The starting shape parameter `M = 2n² + 2dq²` at `dq = 1`. -/
def MOf (G : QuantumMaxCutEnergy.Input) : ℚ := 2 * (G.n : ℚ) ^ 2 + 2 * (1 : ℚ) ^ 2

/-- The base whose `N`-th power is `2Φ₀ / r^N`: `√M · 8(Rq+1)`. -/
def baseA (G : QuantumMaxCutEnergy.Input) : ℝ :=
  Real.sqrt (((MOf G : ℚ) : ℝ)) * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))

theorem MOf_pos (G : QuantumMaxCutEnergy.Input) : 0 < MOf G := by
  have h : (0 : ℚ) ≤ (G.n : ℚ) ^ 2 := sq_nonneg _
  simp only [MOf]; nlinarith

theorem Rq_cast_nonneg (G : QuantumMaxCutEnergy.Input) :
    (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by
  have h : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G := QMCLeafB.EngineRuntime.Rq_nonneg G
  exact_mod_cast h

theorem one_le_baseA (G : QuantumMaxCutEnergy.Input) : 1 ≤ baseA G := by
  have hM : (1 : ℝ) ≤ ((MOf G : ℚ) : ℝ) := by
    have h2 : (1 : ℚ) ≤ MOf G := by
      simp only [MOf]
      have : (0 : ℚ) ≤ (G.n : ℚ) ^ 2 := sq_nonneg _
      nlinarith
    exact_mod_cast h2
  have hsq : (1 : ℝ) ≤ Real.sqrt (((MOf G : ℚ) : ℝ)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hM
  have hq := Rq_cast_nonneg G
  have h8 : (1 : ℝ) ≤ 8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) := by linarith
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ Real.sqrt (((MOf G : ℚ) : ℝ)) * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1)) :=
        mul_le_mul hsq h8 (by norm_num) (by linarith)
    _ = baseA G := rfl

/-- **The potential identity**: `2Φ₀ / r^N = 2 · (baseA G)^N` at `dq = 1`. -/
theorem two_pot_div (G : QuantumMaxCutEnergy.Input) :
    2 * QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (MOf G))
      / ((((1 : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n))
      = 2 * (baseA G) ^ (G.n * G.n) := by
  have hΦ : QMCLeafB.EngineIterates.volPot (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (MOf G))
      = (Real.sqrt (((MOf G : ℚ) : ℝ))) ^ (G.n * G.n) :=
    QMCLeafB.Boundary.volPot_initShapeOf _ (MOf_pos G)
  have hr : ((((1 : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))))
      = (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))⁻¹ := by
    simp only [Rat.cast_one, one_div]
  have hmul : (Real.sqrt (((MOf G : ℚ) : ℝ))) ^ (G.n * G.n)
      * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1)) ^ (G.n * G.n)
      = (Real.sqrt (((MOf G : ℚ) : ℝ))
          * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n) :=
    (mul_pow _ _ _).symm
  calc 2 * QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (MOf G))
        / ((((1 : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n))
      = 2 * (Real.sqrt (((MOf G : ℚ) : ℝ))) ^ (G.n * G.n)
          / (((8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))⁻¹) ^ (G.n * G.n)) := by
        rw [hΦ, hr]
    _ = 2 * ((Real.sqrt (((MOf G : ℚ) : ℝ))) ^ (G.n * G.n)
          * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1)) ^ (G.n * G.n)) := by
        rw [inv_pow, div_inv_eq_mul]
        ring
    _ = 2 * (Real.sqrt (((MOf G : ℚ) : ℝ))
          * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n) := by
        rw [hmul]
    _ = 2 * (baseA G) ^ (G.n * G.n) := by rw [baseA]

/-! ## 3.  The `Nat.clog` core -/

/-- **The round count.**  `budgetRounds G 1 m ≤ m · ((n²+1) · (Nat.clog 2 ⌈baseA⌉ + 2))`. -/
theorem budgetRounds_le_clog (G : QuantumMaxCutEnergy.Input) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G 1 m
      ≤ m * ((G.n * G.n + 1) * (Nat.clog 2 (Nat.ceil (baseA G)) + 2)) := by
  have hs1 : 1 ≤ Nat.ceil (baseA G) := by
    have hb : (1 : ℝ) ≤ baseA G := one_le_baseA G
    have hc := Nat.le_ceil (baseA G)
    have hpos : (0 : ℝ) < ((Nat.ceil (baseA G) : ℕ) : ℝ) :=
      lt_of_lt_of_le (by norm_num) (le_trans hb hc)
    have hpos' : 0 < Nat.ceil (baseA G) := by exact_mod_cast hpos
    exact Nat.succ_le_of_lt hpos'
  rcases Nat.eq_zero_or_pos G.n with hn0 | hnpos
  · -- `n = 0`: the potential is `1`, the radius `1`, so one round suffices
    have hbud : QMCLeafB.FinalStroke.budgetRounds G 1 m = m := by
      unfold QMCLeafB.FinalStroke.budgetRounds QMCLeafB.SimLoop.simRounds
      rw [hn0]
      have hΦ : QMCLeafB.EngineIterates.volPot (0 * 0)
          (QMCLeafB.Boundary.initShapeOf (0 * 0)
            (2 * (↑(0 : ℕ) : ℚ) ^ 2 + 2 * ((1 : ℚ)) ^ 2)) = 1 := by
        rw [QMCLeafB.Boundary.volPot_initShapeOf (0 * 0) (by norm_num)]
        simp
      rw [hΦ]
      norm_num
    rw [hbud, hn0]
    have h0 : 0 ≤ Nat.clog 2 (Nat.ceil (baseA G)) := Nat.zero_le _
    nlinarith
  · -- `n ≥ 1`: exponentiate
    have hN1 : 1 ≤ G.n * G.n := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hsAle : baseA G ≤ ((Nat.ceil (baseA G) : ℕ) : ℝ) := Nat.le_ceil _
    have hnon : (0 : ℝ) ≤ baseA G := le_trans (by norm_num) (one_le_baseA G)
    have h2N : (2 : ℝ) ≤ (2 : ℝ) ^ (G.n * G.n) := by
      have := two_le_two_pow (N := G.n * G.n) hN1
      have h : ((2 : ℕ) : ℝ) ≤ (((2 : ℕ) ^ (G.n * G.n) : ℕ) : ℝ) := by exact_mod_cast this
      simpa using h
    have hstep : ⌈2 * QMCLeafB.EngineIterates.volPot (G.n * G.n)
          (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (MOf G))
        / ((((1 : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n))⌉₊
        ≤ (((2 * Nat.ceil (baseA G)) ^ (G.n * G.n) : ℕ)) := by
      rw [two_pot_div G]
      refine Nat.ceil_le.mpr ?_
      calc 2 * (baseA G) ^ (G.n * G.n)
            ≤ 2 * ((Nat.ceil (baseA G) : ℕ) : ℝ) ^ (G.n * G.n) := by
              have h1 : (baseA G) ^ (G.n * G.n) ≤ ((Nat.ceil (baseA G) : ℕ) : ℝ) ^ (G.n * G.n) :=
                pow_le_pow_left₀ hnon hsAle _
              linarith
        _ ≤ (2 : ℝ) ^ (G.n * G.n) * ((Nat.ceil (baseA G) : ℕ) : ℝ) ^ (G.n * G.n) := by
              have hs : (0 : ℝ) ≤ ((Nat.ceil (baseA G) : ℕ) : ℝ) ^ (G.n * G.n) := by positivity
              nlinarith
        _ = ((2 : ℝ) * ((Nat.ceil (baseA G) : ℕ) : ℝ)) ^ (G.n * G.n) := by rw [mul_pow]
        _ = ((((2 * Nat.ceil (baseA G)) ^ (G.n * G.n) : ℕ)) : ℝ) := by push_cast; ring
    have hclog : Nat.clog 2 ⌈2 * QMCLeafB.EngineIterates.volPot (G.n * G.n)
          (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (MOf G))
        / ((((1 : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n))⌉₊
        ≤ G.n * G.n * (Nat.clog 2 (Nat.ceil (baseA G)) + 1) := by
      refine (Nat.clog_le_iff_le_pow (by norm_num)).mpr ?_
      refine le_trans hstep ?_
      have h2s : (2 * Nat.ceil (baseA G)) ^ (G.n * G.n)
          ≤ (2 ^ (Nat.clog 2 (Nat.ceil (baseA G)) + 1)) ^ (G.n * G.n) := by
        apply Nat.pow_le_pow_left
        have h1 : Nat.ceil (baseA G) ≤ 2 ^ Nat.clog 2 (Nat.ceil (baseA G)) :=
          Nat.le_pow_clog (by norm_num) _
        calc 2 * Nat.ceil (baseA G) ≤ 2 * 2 ^ Nat.clog 2 (Nat.ceil (baseA G)) := by omega
          _ = 2 ^ (Nat.clog 2 (Nat.ceil (baseA G)) + 1) := by rw [pow_succ]; ring
      calc (2 * Nat.ceil (baseA G)) ^ (G.n * G.n)
          ≤ (2 ^ (Nat.clog 2 (Nat.ceil (baseA G)) + 1)) ^ (G.n * G.n) := h2s
        _ = 2 ^ (G.n * G.n * (Nat.clog 2 (Nat.ceil (baseA G)) + 1)) := by
            rw [← pow_mul, Nat.mul_comm]
    have hbud : QMCLeafB.FinalStroke.budgetRounds G 1 m
        = Nat.clog 2 ⌈2 * QMCLeafB.EngineIterates.volPot (G.n * G.n)
            (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (MOf G))
          / ((((1 : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n))⌉₊
          * m := rfl
    rw [hbud, Nat.mul_comm m]
    refine Nat.mul_le_mul_right m ?_
    refine le_trans hclog ?_
    have h0 : 0 ≤ Nat.clog 2 (Nat.ceil (baseA G)) := Nat.zero_le _
    nlinarith


/-! ## 4.  From `⌈baseA⌉` to `⌈Rq⌉` and `n` -/

/-- `⌈baseA⌉ ≤ 16(n+1)(⌈Rq⌉+1)`: the starting radius is at most `2(n+1)`, and `Rq` is at most its
own ceiling. -/
theorem ceil_baseA_le (G : QuantumMaxCutEnergy.Input) :
    Nat.ceil (baseA G) ≤ 16 * (G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) := by
  have hqle : ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ)
      ≤ ((Nat.ceil (QMCLeafB.EngineRuntime.Rq G) : ℕ) : ℝ) := by
    have h := Nat.le_ceil (QMCLeafB.EngineRuntime.Rq G)
    simpa using h
  have hMle : (((MOf G : ℚ) : ℝ)) ≤ (2 * ((G.n : ℕ) : ℝ) + 2) ^ 2 := by
    have hM : MOf G = 2 * (G.n : ℚ) ^ 2 + 2 := by
      simp only [MOf]; norm_num
    rw [hM]
    have hcast : (((2 * (G.n : ℚ) ^ 2 + 2 : ℚ)) : ℝ)
        = 2 * ((G.n : ℕ) : ℝ) ^ 2 + 2 := by push_cast; ring
    rw [hcast]
    nlinarith [Nat.cast_nonneg (α := ℝ) G.n, sq_nonneg ((G.n : ℝ))]
  have hsqrt : Real.sqrt (((MOf G : ℚ) : ℝ)) ≤ 2 * ((G.n : ℕ) : ℝ) + 2 := by
    have h0 : (0 : ℝ) ≤ 2 * ((G.n : ℕ) : ℝ) + 2 := by positivity
    calc Real.sqrt (((MOf G : ℚ) : ℝ)) ≤ Real.sqrt ((2 * ((G.n : ℕ) : ℝ) + 2) ^ 2) :=
          Real.sqrt_le_sqrt hMle
      _ = 2 * ((G.n : ℕ) : ℝ) + 2 := Real.sqrt_sq h0
  have hbase : baseA G ≤ ((16 * (G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) : ℕ) : ℝ) := by
    have hq : (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))
        ≤ 8 * (((Nat.ceil (QMCLeafB.EngineRuntime.Rq G) : ℕ) : ℝ) + 1) := by linarith
    calc baseA G = Real.sqrt (((MOf G : ℚ) : ℝ))
          * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1)) := rfl
      _ ≤ (2 * ((G.n : ℕ) : ℝ) + 2)
            * (8 * (((Nat.ceil (QMCLeafB.EngineRuntime.Rq G) : ℕ) : ℝ) + 1)) :=
          mul_le_mul hsqrt hq
            (by linarith [Nat.cast_nonneg (α := ℝ) (Nat.ceil (QMCLeafB.EngineRuntime.Rq G)),
              Rq_cast_nonneg G])
            (by linarith [Nat.cast_nonneg (α := ℝ) G.n])
      _ = ((16 * (G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) : ℕ) : ℝ) := by
          push_cast; ring
  calc Nat.ceil (baseA G)
      ≤ Nat.ceil (((16 * (G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) : ℕ) : ℝ)) :=
        Nat.ceil_le_ceil hbase
    _ = 16 * (G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) := Nat.ceil_natCast _

/-- **`Nat.clog 2 ⌈baseA⌉ ≤ ⌈Rq⌉ + n + 6`**: the log of the starting potential is bounded by the
input's total weight plus the dimension. -/
theorem clog_baseA_le (G : QuantumMaxCutEnergy.Input) :
    Nat.clog 2 (Nat.ceil (baseA G))
      ≤ Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n + 6 := by
  have hmono : Nat.clog 2 (Nat.ceil (baseA G))
      ≤ Nat.clog 2 (16 * (G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1)) :=
    Nat.clog_mono_right 2 (ceil_baseA_le G)
  have h1 : Nat.clog 2 (16 * (G.n + 1)) ≤ Nat.clog 2 16 + Nat.clog 2 (G.n + 1) :=
    clog_two_mul_le (x := 16) (y := G.n + 1) (by norm_num) (by omega)
  have h2 : Nat.clog 2 (16 * (G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1))
      ≤ Nat.clog 2 (16 * (G.n + 1)) + Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) :=
    clog_two_mul_le (x := 16 * (G.n + 1)) (y := Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1)
      (by omega) (by omega)
  have h16 : Nat.clog 2 16 = 4 := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.clog_pow 2 4 (by norm_num)]
  have hd : Nat.clog 2 (G.n + 1) ≤ G.n + 1 := clog_two_le_self (by omega)
  omega

/-- **The round-count bound, in `log` form**: `budgetRounds G 1 m ≤ m·(n²+1)·(log⌈Rq⌉ + n + 8)`.
This is the shape the fuel wants: the `clog` is what survives the passage to the input length. -/
theorem budgetRounds_le_log (G : QuantumMaxCutEnergy.Input) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G 1 m
      ≤ m * ((G.n * G.n + 1)
          * (Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n + 8)) := by
  refine le_trans (budgetRounds_le_clog G m) ?_
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_left
  have := clog_baseA_le G
  omega

/-- **The round-count bound.**  `budgetRounds G 1 m ≤ m·(n²+1)·(⌈Rq G⌉ + n + 8)`: cubic in the
dimension and linear in the total weight. -/
theorem budgetRounds_le_value (G : QuantumMaxCutEnergy.Input) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G 1 m
      ≤ m * ((G.n * G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + G.n + 8)) := by
  refine le_trans (budgetRounds_le_log G m) ?_
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_left
  have h : Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1)
      ≤ Nat.ceil (QMCLeafB.EngineRuntime.Rq G) := clog_succ_le _
  omega

/-- **The round count in input-length form.**  Given only that
`clog 2 (⌈Rq G⌉+1) + n + 8 ≤ (L+1)^3` — which holds for `L = (encodeRequest p.1).length` because a
rational's denotation is bounded by `2` raised to its encoded length — the run is dominated by
`m · (n+1)^3 · (L+1)^3`, i.e. by a monomial in the dimension and the input length, which is what a
`PolyProgram` fuel length needs. -/
theorem budgetRounds_le_monomial (G : QuantumMaxCutEnergy.Input) (m L : ℕ)
    (h : Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n + 8 ≤ (L + 1) ^ 3) :
    QMCLeafB.FinalStroke.budgetRounds G 1 m ≤ m * ((G.n + 1) ^ 3 * (L + 1) ^ 3) := by
  refine le_trans (budgetRounds_le_log G m) ?_
  have hn : G.n * G.n + 1 ≤ (G.n + 1) ^ 3 := by nlinarith
  have hcl : Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n + 8 ≤ (L + 1) ^ 3 := h
  calc m * ((G.n * G.n + 1)
        * (Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n + 8))
      ≤ m * ((G.n + 1) ^ 3 * (L + 1) ^ 3) := by
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul hn hcl

end QMCLeafB.BudgetBound

/-! ## 5.  Axiom audit -/

#print axioms QMCLeafB.BudgetBound.clog_two_le_self
#print axioms QMCLeafB.BudgetBound.clog_two_mul_le
#print axioms QMCLeafB.BudgetBound.two_le_two_pow
#print axioms QMCLeafB.BudgetBound.one_le_baseA
#print axioms QMCLeafB.BudgetBound.two_pot_div
#print axioms QMCLeafB.BudgetBound.budgetRounds_le_clog
#print axioms QMCLeafB.BudgetBound.ceil_baseA_le
#print axioms QMCLeafB.BudgetBound.clog_baseA_le
#print axioms QMCLeafB.BudgetBound.succ_le_two_pow
#print axioms QMCLeafB.BudgetBound.clog_succ_le
#print axioms QMCLeafB.BudgetBound.budgetRounds_le_log
#print axioms QMCLeafB.BudgetBound.budgetRounds_le_value
#print axioms QMCLeafB.BudgetBound.budgetRounds_le_monomial


