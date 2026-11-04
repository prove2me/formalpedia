-- Prove2me | Definitions.Def_QMCLeafB_count_estimate_m4
-- name    : QMCLeafB_count_estimate_m4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:44:01.029193+00:00
-- url     : https://prove2.me/theorems/de1fae43-ac92-4468-8255-ec583928b01d
-- title:
--   QMCLeafB count_estimate_m4
-- statement:
--   # leaf B phase 13 — brick `count-estimate` (swarm `smw17fzqq`, member m4, direction d12)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_hspec_m4
import Definitions.Def_QMCLeafB_final_stroke_m7
/-
# leaf B phase 13 — brick `count-estimate` (swarm `smw17fzqq`, member m4, direction d12)

The last analytic step of the round count.  `RunParams.hbudget` needs a `K` above
`SimLoop.simRounds`; the fuel needs `K * m` to be a `Poly` function of the input
(`Check_spec`… see `Check_hspec_m4` §3j, which proves `countK` Poly and under the fuel length).  What
is missing is the *estimate*

    simRounds n Φ₀ r m  ≤  (n+1)^6 * (bitCost (Rq G) + 1) * m,

i.e. `Nat.clog 2 ⌈2Φ₀/r^{n²}⌉ ≤ (n+1)^6 (bitCost (Rq G) + 1)`.  This file proves it, in two
independent halves:

* §1 the initial potential: `volPot N (initShapeOf N M) ≤ M^N` — `initShapeOf N M = M⁻¹ • 1`, so its
  determinant is `M^{-N}` and `√x ≥ x` for `x ≤ 1` turns `(√(M^{-N}))⁻¹` into at most `M^N`;
* §2 the logarithm: `Rq + 1 ≤ 2 ^ bitCost (Rq G)` (`Check_hspec_m4`), `n + 1 ≤ 2 ^ (n+1)`, and
  `Nat.clog_le_iff_le_pow`, with the exponent arithmetic done in `ℕ`.

No σ, no programs, no integration; `bitCost` and `countK` come from `Check_hspec_m4`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.CountEstimate

open QuantumMaxCutEnergy

/-! ## 1.  The initial potential is at most `M ^ N` -/

/-- The determinant of the starting shape: `(M⁻¹)^N`. -/
theorem det_initShapeOf (N : ℕ) (M : ℚ) :
    (QMCLeafB.Boundary.initShapeOf N M).det = M⁻¹ ^ N := by
  rw [QMCLeafB.Boundary.initShapeOf, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin]

/-- **`volPot N (initShapeOf N M) ≤ M ^ N`** for `M ≥ 1`.  (`volPot` is `(√det)⁻¹`; `det = M^{-N}`
lies in `(0, 1]`, and `√x ≥ x` there.) -/
theorem volPot_initShapeOf_le (N : ℕ) (M : ℚ) (hM : 1 ≤ M) :
    QMCLeafB.EngineIterates.volPot N (QMCLeafB.Boundary.initShapeOf N M) ≤ (M : ℝ) ^ N := by
  have hMpos : (0 : ℚ) < M := by linarith
  have hMposR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have hdet : QMCLeafB.EngineIterates.volPot N (QMCLeafB.Boundary.initShapeOf N M)
      = (Real.sqrt (((M : ℝ)⁻¹) ^ N))⁻¹ := by
    rw [QMCLeafB.EngineIterates.volPot, QMCLeafB.Boundary.castM_initShapeOf,
      Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hx1 : ((M : ℝ)⁻¹) ^ N ≤ 1 := by
    have h1 : (M : ℝ)⁻¹ ≤ 1 := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      exact inv_le_one_of_one_le₀ this
    exact pow_le_one₀ (by positivity) h1
  have hx0 : (0 : ℝ) < ((M : ℝ)⁻¹) ^ N := by positivity
  have hsqrt : ((M : ℝ)⁻¹) ^ N ≤ Real.sqrt (((M : ℝ)⁻¹) ^ N) := by
    have hsq : (((M : ℝ)⁻¹) ^ N) ^ 2 ≤ ((M : ℝ)⁻¹) ^ N := by
      nlinarith [hx0, hx1]
    calc ((M : ℝ)⁻¹) ^ N = Real.sqrt ((((M : ℝ)⁻¹) ^ N) ^ 2) := (Real.sqrt_sq (le_of_lt hx0)).symm
      _ ≤ Real.sqrt (((M : ℝ)⁻¹) ^ N) := Real.sqrt_le_sqrt hsq
  have hinv : (Real.sqrt (((M : ℝ)⁻¹) ^ N))⁻¹ ≤ (((M : ℝ)⁻¹) ^ N)⁻¹ :=
    inv_le_inv₀ (Real.sqrt_pos.2 hx0) hx0 |>.mpr hsqrt
  rw [hdet]
  refine hinv.trans (le_of_eq ?_)
  rw [← inv_pow, inv_inv]

/-! ## 2.  The logarithm

With §1 the ratio is `2Φ₀/r^{n²} ≤ 2·(2(n+1)²)^{n²}·(8(Rq+1))^{n²}`, and both factors are under
powers of two: `n+1 ≤ 2^(n+1)` and `Rq + 1 ≤ 2^(bitCost Rq)`.  So the whole ratio is under
`2 ^ (1 + bitCost·n² + 4n² + 2n²(n+1))`, and that exponent is below `(n+1)^6 (bitCost + 1)`; then
`Nat.clog_le_iff_le_pow`. -/

/-- The starting shape's parameter `M = 2n² + 2` is at most `2(n+1)²`. -/
theorem shapeM_le (n : ℕ) : 2 * (n : ℚ) ^ 2 + 2 ≤ 2 * ((n : ℚ) + 1) ^ 2 := by
  nlinarith [Nat.cast_nonneg (α := ℚ) n]

/-- The starting shape's parameter is at least `1`. -/
theorem one_le_shapeM (n : ℕ) : (1 : ℚ) ≤ 2 * (n : ℚ) ^ 2 + 2 := by
  nlinarith [Nat.cast_nonneg (α := ℚ) n]

/-- **The ratio is under a power of two.** -/
theorem ratio_le_two_pow (n : ℕ) (Rq : ℚ) (hRq : 0 ≤ Rq) :
    2 * QMCLeafB.EngineIterates.volPot (n * n)
        (QMCLeafB.Boundary.initShapeOf (n * n) (2 * (n : ℚ) ^ 2 + 2))
      / (1 / (8 * ((Rq : ℝ) + 1))) ^ (n * n)
      ≤ (2 : ℝ) ^ (1 + QMCLeafB.Hspec.bitCost Rq * (n * n) + 4 * (n * n)
        + 2 * (n * n) * (n + 1)) := by
  have hRqR : (0 : ℝ) ≤ (Rq : ℝ) := by exact_mod_cast hRq
  have hpos : (0 : ℝ) < (Rq : ℝ) + 1 := by linarith
  -- the inverse radius is `8 (Rq+1)`
  have hinv : ((1 : ℝ) / (8 * ((Rq : ℝ) + 1)))⁻¹ = 8 * ((Rq : ℝ) + 1) := by
    rw [inv_div]
    simp
  -- `Φ₀ ≤ (2 (n+1)²)^{n²}`
  have hΦ : QMCLeafB.EngineIterates.volPot (n * n)
      (QMCLeafB.Boundary.initShapeOf (n * n) (2 * (n : ℚ) ^ 2 + 2))
      ≤ (2 * ((n : ℝ) + 1) ^ 2) ^ (n * n) := by
    refine (volPot_initShapeOf_le (n * n) (2 * (n : ℚ) ^ 2 + 2) (one_le_shapeM n)).trans ?_
    have hcast : ((2 * (n : ℚ) ^ 2 + 2 : ℚ) : ℝ) = 2 * ((n : ℝ)) ^ 2 + 2 := by push_cast; ring
    rw [hcast]
    have h2 : 2 * (n : ℝ) ^ 2 + 2 ≤ 2 * ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have h0 : (0 : ℝ) ≤ 2 * (n : ℝ) ^ 2 + 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    exact pow_le_pow_left₀ h0 h2 (n * n)
  -- `8 (Rq+1) ≤ 2^(bitCost+3)`
  have hRqpow : ((Rq : ℝ) + 1) ≤ (2 : ℝ) ^ QMCLeafB.Hspec.bitCost Rq := by
    have h := QMCLeafB.Hspec.rat_add_one_le_two_pow_bitCost Rq hRq
    calc (Rq : ℝ) + 1 = (((Rq + 1 : ℚ)) : ℝ) := by push_cast; ring
      _ ≤ (((2 : ℚ) ^ QMCLeafB.Hspec.bitCost Rq : ℚ) : ℝ) := by exact_mod_cast h
      _ = (2 : ℝ) ^ QMCLeafB.Hspec.bitCost Rq := by push_cast; ring
  have h8 : 8 * ((Rq : ℝ) + 1) ≤ (2 : ℝ) ^ (QMCLeafB.Hspec.bitCost Rq + 3) := by
    have h8' : (8 : ℝ) = 2 ^ 3 := by norm_num
    calc 8 * ((Rq : ℝ) + 1) ≤ 8 * (2 : ℝ) ^ QMCLeafB.Hspec.bitCost Rq := by
          exact mul_le_mul_of_nonneg_left hRqpow (by norm_num)
      _ = (2 : ℝ) ^ (QMCLeafB.Hspec.bitCost Rq + 3) := by
          rw [h8', ← pow_add]; ring_nf
  -- `n+1 ≤ 2^(n+1)`
  have hnp1 : ((n : ℝ) + 1) ≤ (2 : ℝ) ^ (n + 1) := by
    have h : (n + 1 : ℕ) < 2 ^ (n + 1) := Nat.lt_two_pow_self
    have h2 : ((n + 1 : ℕ) : ℝ) ≤ ((2 ^ (n + 1) : ℕ) : ℝ) := by
      exact_mod_cast le_of_lt h
    push_cast at h2 ⊢
    exact h2
  rw [div_eq_mul_inv, ← inv_pow, hinv]
  -- assemble
  have hpow : ((2 : ℝ) ^ (QMCLeafB.Hspec.bitCost Rq + 3)) ^ (n * n)
      = (2 : ℝ) ^ ((QMCLeafB.Hspec.bitCost Rq + 3) * (n * n)) := by
    rw [← pow_mul]
  have hpow2 : ((2 * ((n : ℝ) + 1) ^ 2)) ^ (n * n)
      = (2 : ℝ) ^ (n * n) * (((n : ℝ) + 1) ^ 2) ^ (n * n) := mul_pow _ _ _
  have hpow3 : (((n : ℝ) + 1) ^ 2) ^ (n * n) ≤ ((2 : ℝ) ^ (n + 1)) ^ (2 * (n * n)) := by
    have h0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by positivity
    calc (((n : ℝ) + 1) ^ 2) ^ (n * n) = ((n : ℝ) + 1) ^ (2 * (n * n)) := by
          rw [← pow_mul]
      _ ≤ ((2 : ℝ) ^ (n + 1)) ^ (2 * (n * n)) := by
          apply pow_le_pow_left₀ (by positivity) hnp1
  have hexp : ((2 : ℝ) ^ (n + 1)) ^ (2 * (n * n))
      = (2 : ℝ) ^ ((n + 1) * (2 * (n * n))) := by rw [← pow_mul]
  calc 2 * QMCLeafB.EngineIterates.volPot (n * n)
        (QMCLeafB.Boundary.initShapeOf (n * n) (2 * (n : ℚ) ^ 2 + 2)) * (8 * ((Rq : ℝ) + 1)) ^ (n * n)
      = 2 * (QMCLeafB.EngineIterates.volPot (n * n)
          (QMCLeafB.Boundary.initShapeOf (n * n) (2 * (n : ℚ) ^ 2 + 2)) * (8 * ((Rq : ℝ) + 1)) ^ (n * n)) := by
        ring
    _ ≤ 2 * ((2 * ((n : ℝ) + 1) ^ 2) ^ (n * n)
          * ((2 : ℝ) ^ (QMCLeafB.Hspec.bitCost Rq + 3)) ^ (n * n)) := by
        have h9 : (0 : ℝ) ≤ 8 * ((Rq : ℝ) + 1) := by positivity
        have := mul_le_mul hΦ (pow_le_pow_left₀ h9 h8 (n * n)) (by positivity)
          (by positivity)
        exact mul_le_mul_of_nonneg_left this (by norm_num)
    _ = 2 * ((2 : ℝ) ^ (n * n) * (((n : ℝ) + 1) ^ 2) ^ (n * n)
          * (2 : ℝ) ^ ((QMCLeafB.Hspec.bitCost Rq + 3) * (n * n))) := by
        rw [hpow2, hpow]
    _ ≤ 2 * ((2 : ℝ) ^ (n * n)
          * (((2 : ℝ) ^ (n + 1)) ^ (2 * (n * n)))
          * (2 : ℝ) ^ ((QMCLeafB.Hspec.bitCost Rq + 3) * (n * n))) := by
        have hA : (0 : ℝ) ≤ (2 : ℝ) ^ (n * n) := by positivity
        have hB : (0 : ℝ) ≤ (2 : ℝ) ^ ((QMCLeafB.Hspec.bitCost Rq + 3) * (n * n)) := by positivity
        have := mul_le_mul_of_nonneg_left hpow3 (by positivity : (0:ℝ) ≤ (2:ℝ)^(n*n))
        have h2' := mul_le_mul_of_nonneg_right this hB
        exact mul_le_mul_of_nonneg_left h2' (by norm_num)
    _ = (2 : ℝ) ^ (1 + QMCLeafB.Hspec.bitCost Rq * (n * n) + 4 * (n * n)
          + 2 * (n * n) * (n + 1)) := by
        rw [hexp]
        have hE : (n * n + (n + 1) * (2 * (n * n))) + (QMCLeafB.Hspec.bitCost Rq + 3) * (n * n)
            = QMCLeafB.Hspec.bitCost Rq * (n * n) + 4 * (n * n) + 2 * (n * n) * (n + 1) := by
          ring
        rw [← pow_add, ← pow_add, hE]
        conv_lhs => arg 1; rw [show (2 : ℝ) = 2 ^ 1 from (pow_one 2).symm]
        rw [← pow_add]
        congr 1
        omega

/-! ## 3.  The exponent arithmetic -/

/-- `n² ≤ (n+1)^8`. -/
theorem sq_le_succ_pow (n : ℕ) : n * n ≤ (n + 1) ^ 8 := by
  have h : n * n ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n)
  have h2 : (n + 1) * (n + 1) = (n + 1) ^ 2 := by ring
  have h3 : (n + 1) ^ 2 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- `1 + 4n² + 2n²(n+1) ≤ (n+1)^8`. -/
theorem one_add_four_sq_add_le (n : ℕ) : 1 + 4 * (n * n) + 2 * (n * n) * (n + 1) ≤ (n + 1) ^ 8 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · have h6 : 26 ≤ (n + 1) ^ 5 := by
      calc 26 ≤ 32 := by norm_num
        _ = 2 ^ 5 := by norm_num
        _ ≤ (n + 1) ^ 5 := Nat.pow_le_pow_left (by omega) 5
    have hn1 : n ≤ n + 1 := Nat.le_succ n
    have h3 : n + 3 ≤ 3 * (n + 1) := by omega
    have hstep : 2 * (n * n) * (n + 3) ≤ 2 * ((n + 1) * (n + 1)) * (3 * (n + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (le_refl 2) (Nat.mul_le_mul hn1 hn1)) h3
    have hX : (1 : ℕ) ≤ (n + 1) ^ 3 := Nat.one_le_pow 3 (n + 1) (by omega)
    calc 1 + 4 * (n * n) + 2 * (n * n) * (n + 1) = 1 + 2 * (n * n) * (n + 3) := by ring
      _ ≤ 1 + 2 * ((n + 1) * (n + 1)) * (3 * (n + 1)) := by omega
      _ = 1 + 6 * (n + 1) ^ 3 := by ring
      _ ≤ 26 * (n + 1) ^ 3 := by omega
      _ ≤ (n + 1) ^ 5 * (n + 1) ^ 3 := Nat.mul_le_mul_right _ h6
      _ = (n + 1) ^ 8 := by ring

/-- **The exponent bound**: `1 + bitCost·n² + 4n² + 2n²(n+1) ≤ (n+1)^8 (bitCost + 1)`. -/
theorem exp_le (n bc : ℕ) :
    1 + bc * (n * n) + 4 * (n * n) + 2 * (n * n) * (n + 1) ≤ (n + 1) ^ 8 * (bc + 1) := by
  have hsq := sq_le_succ_pow n
  have h23 := one_add_four_sq_add_le n
  have h1 : bc * (n * n) ≤ (n + 1) ^ 8 * bc := by
    refine (Nat.mul_le_mul_left bc hsq).trans ?_
    exact le_of_eq (Nat.mul_comm bc ((n + 1) ^ 8))
  have hfin : (n + 1) ^ 8 * (bc + 1) = (n + 1) ^ 8 * bc + (n + 1) ^ 8 := by
    rw [Nat.mul_add, Nat.mul_one]
  omega

/-! ## 4.  `Nat.clog` -/

/-- **The logarithm estimate.** -/
theorem clog_le (n : ℕ) (Rq : ℚ) (hRq : 0 ≤ Rq) :
    Nat.clog 2 ⌈2 * QMCLeafB.EngineIterates.volPot (n * n)
        (QMCLeafB.Boundary.initShapeOf (n * n) (2 * (n : ℚ) ^ 2 + 2))
      / (1 / (8 * ((Rq : ℝ) + 1))) ^ (n * n)⌉₊
      ≤ (n + 1) ^ 8 * (QMCLeafB.Hspec.bitCost Rq + 1) := by
  have hX := ratio_le_two_pow n Rq hRq
  have hE := exp_le n (QMCLeafB.Hspec.bitCost Rq)
  have h2E : (2 : ℝ) ^ (1 + QMCLeafB.Hspec.bitCost Rq * (n * n) + 4 * (n * n)
        + 2 * (n * n) * (n + 1))
      ≤ (2 : ℝ) ^ ((n + 1) ^ 8 * (QMCLeafB.Hspec.bitCost Rq + 1)) :=
    pow_le_pow_right₀ (by norm_num) hE
  have hXK : 2 * QMCLeafB.EngineIterates.volPot (n * n)
        (QMCLeafB.Boundary.initShapeOf (n * n) (2 * (n : ℚ) ^ 2 + 2))
      / (1 / (8 * ((Rq : ℝ) + 1))) ^ (n * n)
      ≤ (2 : ℝ) ^ ((n + 1) ^ 8 * (QMCLeafB.Hspec.bitCost Rq + 1)) := hX.trans h2E
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  rw [Nat.ceil_le]
  refine hXK.trans (le_of_eq ?_)
  push_cast
  ring

/-! ## 5.  The round-count estimate in the driver's own terms -/

/-- **`budgetRounds ≤ countK`**: at the campaign's constants (`dq = 1`, `m = 4n²`) the round-count
budget is under the `Poly`-computable count of `Check_hspec_m4` §3j.  This is exactly the `hK`
argument of `FinalStroke.endgame_of_dominated_rounds` / its per-graph `RunParams` form, so `hbudget`
is discharged for the polynomial count and the fuel slot of §3j applies. -/
theorem budgetRounds_le_countK (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) :
    QMCLeafB.FinalStroke.budgetRounds G 1 (4 * (G.n * G.n))
      ≤ QMCLeafB.Hspec.countK 1 8 G := by
  have hn1 : ¬ (G.n ≤ 1) := by omega
  have hbud : QMCLeafB.FinalStroke.budgetRounds G 1 (4 * (G.n * G.n))
      = Nat.clog 2 ⌈2 * QMCLeafB.EngineIterates.volPot (G.n * G.n)
          (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2))
        / (1 / (8 * ((QMCLeafB.EngineRuntime.Rq G : ℝ) + 1))) ^ (G.n * G.n)⌉₊
        * (4 * (G.n * G.n)) := by
    rw [QMCLeafB.FinalStroke.budgetRounds, QMCLeafB.SimLoop.simRounds]
    norm_num
  have hcount : QMCLeafB.Hspec.countK 1 8 G
      = (G.n + 1) ^ 8 * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1)
        * (4 * (G.n * G.n)) := by
    rw [QMCLeafB.Hspec.countK]
    simp only [if_neg hn1, Nat.one_mul]
  rw [hbud, hcount]
  exact Nat.mul_le_mul_right _
    (clog_le G.n (QMCLeafB.EngineRuntime.Rq G) (QMCLeafB.EngineRuntime.Rq_nonneg G))

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.CountEstimate.det_initShapeOf
#print axioms QMCLeafB.CountEstimate.volPot_initShapeOf_le
#print axioms QMCLeafB.CountEstimate.shapeM_le
#print axioms QMCLeafB.CountEstimate.one_le_shapeM
#print axioms QMCLeafB.CountEstimate.ratio_le_two_pow
#print axioms QMCLeafB.CountEstimate.sq_le_succ_pow
#print axioms QMCLeafB.CountEstimate.one_add_four_sq_add_le
#print axioms QMCLeafB.CountEstimate.exp_le
#print axioms QMCLeafB.CountEstimate.clog_le
#print axioms QMCLeafB.CountEstimate.budgetRounds_le_countK

end QMCLeafB.CountEstimate


