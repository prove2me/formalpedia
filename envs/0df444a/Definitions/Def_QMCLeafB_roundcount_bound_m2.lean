-- Prove2me | Definitions.Def_QMCLeafB_roundcount_bound_m2
-- name    : QMCLeafB_roundcount_bound_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:02:27.636285+00:00
-- url     : https://prove2.me/theorems/7999ebec-b795-4c7f-a8cb-7ca429c5cf74
-- title:
--   QMCLeafB roundcount_bound_m2
-- statement:
--   # leaf B phase 13 — brick `round-count-bound` (swarm `smw17fqzz`, member m2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ClosingBracket
import Definitions.Def_QMCLeafB_boundary_m2
import Definitions.Def_QMCLeafB_runparams_m2
import Definitions.Def_QMCLeafB_roundcount_m2
/-
# leaf B phase 13 — brick `round-count-bound` (swarm `smw17fqzz`, member m2)

The fuel slot needs the loop's round count `T0 = K · m` to be a **monomial bound** on
`SimLoop.simRounds` (`Nat.clog`-based, hence not `Poly`-computable), while `hbudget` only asks for
`K ≥ simRounds` (see `RoundCountEnlarge.runParams_bigger_K`).  This file supplies the two ingredients
of that estimate that are pure algebra:

* §1 **the initial potential in closed form**: `volPot N (initShapeOf N M) = (√M)^N`.  The shape is
  `M⁻¹ • 1`, so `det = (M⁻¹)^N` and the potential `(√det)⁻¹` is `(√M)^N`.  This is the only place
  the campaign's initial potential is evaluated.
* §2 **the round count under a single numeric hypothesis**: if
  `8 · √M · (cA + 1) / dq ≤ 2^B`, then

      simRounds n (volPot (n·n) (initShapeOf (n·n) M)) (dq/(8(cA+1))) m ≤ (1 + n·n·B) · m.

  So the `Nat.clog` is eliminated: the round count is a monomial in `B`, which is what `fuelTake`
  and `poly_fuelTake` need (with `B` supplied by a bound on the total weight, e.g.
  `Rq G ≤ 2^(request length)`).

No `sorry`, no `axiom`; audit at the end.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.RoundCountBound

open QuantumMaxCutEnergy

/-! ## 1.  The initial potential in closed form -/

theorem det_initShapeOf (N : ℕ) (M : ℚ) :
    (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf N M)).det
      = ((M : ℝ)⁻¹) ^ N := by
  rw [QMCLeafB.Boundary.castM_initShapeOf, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin]

/-- `√((M⁻¹)^N) = (√M)⁻¹^N`. -/
theorem sqrt_inv_pow (N : ℕ) {M : ℝ} (hM : 0 < M) :
    Real.sqrt ((M⁻¹) ^ N) = (Real.sqrt M)⁻¹ ^ N := by
  induction N with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ, Real.sqrt_inv]

/-- **The initial potential is `(√M)^N`.** -/
theorem volPot_initShapeOf (N : ℕ) {M : ℚ} (hM : 0 < (M : ℝ)) :
    QMCLeafB.EngineIterates.volPot N (QMCLeafB.Boundary.initShapeOf N M)
      = (Real.sqrt (M : ℝ)) ^ N := by
  unfold QMCLeafB.EngineIterates.volPot
  rw [det_initShapeOf N M, sqrt_inv_pow N hM, inv_pow, inv_inv]

/-! ## 2.  The round count under one numeric hypothesis -/

/-- The key product form: `2·Φ₀/r^N = 2·(√M · 8(c_A+1)/dq)^N` where `r = dq/(8(c_A+1))`. -/
theorem two_volPot_div_radius_pow (N : ℕ) {M : ℚ} (hM : 0 < (M : ℝ)) {dq cAq : ℚ}
    (hdq : 0 < (dq : ℝ)) (hcAq : 0 ≤ (cAq : ℝ)) :
    2 * QMCLeafB.EngineIterates.volPot N (QMCLeafB.Boundary.initShapeOf N M)
        / ((dq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ N
      = 2 * (Real.sqrt (M : ℝ) * 8 * ((cAq : ℝ) + 1) / (dq : ℝ)) ^ N := by
  have harg : (Real.sqrt (M : ℝ)) / ((dq : ℝ) / (8 * ((cAq : ℝ) + 1)))
      = Real.sqrt (M : ℝ) * 8 * ((cAq : ℝ) + 1) / (dq : ℝ) := by
    have hd : (0 : ℝ) < (dq : ℝ) := hdq
    have hc : (0 : ℝ) < 8 * ((cAq : ℝ) + 1) := by linarith
    field_simp
  have hdiv : (Real.sqrt (M : ℝ)) ^ N / ((dq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ N
      = (Real.sqrt (M : ℝ) / ((dq : ℝ) / (8 * ((cAq : ℝ) + 1)))) ^ N :=
    (div_pow _ _ _).symm
  rw [QMCLeafB.RoundCountBound.volPot_initShapeOf N hM, ← harg]
  rw [show 2 * (Real.sqrt (M : ℝ)) ^ N / ((dq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ N
        = 2 * ((Real.sqrt (M : ℝ)) ^ N
            / ((dq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ N) from by ring, hdiv]

/-- **`simRounds` under a numeric hypothesis.**  If `8·√M·(c_A+1)/dq ≤ 2^B` and `1 ≤ B`, then the
`Nat.clog` round count is a monomial: `simRounds ≤ (1 + n·n·B)·m`. -/
theorem simRounds_le_of_bound {n : ℕ} (hn : 2 ≤ n) {M : ℚ} (hM : 0 < (M : ℝ))
    {dq cAq : ℚ} (hdq : 0 < (dq : ℝ)) (hcAq : 0 ≤ (cAq : ℝ))
    {B : ℕ} (hB1 : 1 ≤ B)
    (hB : Real.sqrt (M : ℝ) * 8 * ((cAq : ℝ) + 1) / (dq : ℝ) ≤ (2 : ℝ) ^ B)
    (m : ℕ) :
    QMCLeafB.SimLoop.simRounds n
        (QMCLeafB.EngineIterates.volPot (n * n) (QMCLeafB.Boundary.initShapeOf (n * n) M))
        ((dq : ℝ) / (8 * ((cAq : ℝ) + 1))) m
      ≤ (1 + n * n * B) * m := by
  unfold QMCLeafB.SimLoop.simRounds
  -- bound the ceiling, then the `Nat.clog`
  have hbase : (0 : ℝ) < (Real.sqrt (M : ℝ) * 8 * ((cAq : ℝ) + 1) / (dq : ℝ)) := by
    have h1 : (0 : ℝ) < Real.sqrt (M : ℝ) := Real.sqrt_pos.2 hM
    have h2 : (0 : ℝ) < 8 * ((cAq : ℝ) + 1) := by nlinarith
    positivity
  have hratio : 2 * QMCLeafB.EngineIterates.volPot (n * n)
        (QMCLeafB.Boundary.initShapeOf (n * n) M)
        / ((dq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ (n * n)
      ≤ (2 : ℝ) ^ (1 + n * n * B) := by
    rw [two_volPot_div_radius_pow (n * n) hM hdq hcAq]
    have hpow : (Real.sqrt (M : ℝ) * 8 * ((cAq : ℝ) + 1) / (dq : ℝ)) ^ (n * n)
        ≤ ((2 : ℝ) ^ B) ^ (n * n) :=
      pow_le_pow_left₀ (le_of_lt hbase) hB _
    have hgoal : (2 : ℝ) * ((2 : ℝ) ^ B) ^ (n * n) = (2 : ℝ) ^ (1 + n * n * B) := by
      rw [← pow_mul, ← pow_succ']
      congr 1
      ring
    calc 2 * (Real.sqrt (M : ℝ) * 8 * ((cAq : ℝ) + 1) / (dq : ℝ)) ^ (n * n)
        ≤ 2 * ((2 : ℝ) ^ B) ^ (n * n) := by
          exact mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = (2 : ℝ) ^ (1 + n * n * B) := hgoal
  have hlog : Nat.clog 2 ⌈2 * QMCLeafB.EngineIterates.volPot (n * n)
      (QMCLeafB.Boundary.initShapeOf (n * n) M)
      / ((dq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ (n * n)⌉₊ ≤ 1 + n * n * B := by
    rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
    rw [Nat.ceil_le]
    calc 2 * QMCLeafB.EngineIterates.volPot (n * n)
          (QMCLeafB.Boundary.initShapeOf (n * n) M)
          / ((dq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ (n * n)
        ≤ (2 : ℝ) ^ (1 + n * n * B) := hratio
      _ = ((2 ^ (1 + n * n * B) : ℕ) : ℝ) := by push_cast; ring
  exact Nat.mul_le_mul_right m hlog

/-! ## 3.  `RunParams` at a monomial round count

Combining §2 with `RoundCountEnlarge.runParams_bigger_K`: once a caller supplies *any* `B` bounding
`8√M(c_A+1)/dq`, the run's numeric parameters exist at the monomial round factor `(1 + n·n·B)`, i.e.
at a round count that `fuelTake` can produce, rather than at the `Nat.clog`-defined `simRounds`. -/

noncomputable def runParamsOfBound (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (B : ℕ) (hB1 : 1 ≤ B)
    (hB : Real.sqrt (QMCLeafB.RunParamsSupply.runM G : ℝ)
        * 8 * ((QMCLeafB.RunParamsSupply.runCAq G : ℝ) + 1)
        / (QMCLeafB.RunParamsSupply.runDq : ℝ) ≤ (2 : ℝ) ^ B) :
    QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.RoundCountEnlarge.runParams_bigger_K
    (QMCLeafB.RunParamsSupply.runParams G hn)
    ((1 + G.n * G.n * B) * QMCLeafB.RunParamsSupply.runMcount G)
    (by
      have h := simRounds_le_of_bound (n := G.n) hn
        (M := QMCLeafB.RunParamsSupply.runM G)
        (by have h := QMCLeafB.RunParamsSupply.runM_pos G
            exact_mod_cast h)
        (dq := QMCLeafB.RunParamsSupply.runDq)
        (cAq := QMCLeafB.RunParamsSupply.runCAq G)
        (by have h := QMCLeafB.RunParamsSupply.runDq_pos
            exact_mod_cast h)
        (by have h := QMCLeafB.RunParamsSupply.runCAq_nonneg G
            exact_mod_cast h) hB1 hB
        (QMCLeafB.RunParamsSupply.runMcount G)
      simpa only [QMCLeafB.RunParamsSupply.runParams, QMCLeafB.RunParamsSupply.runK,
        QMCLeafB.RunParamsSupply.runPhi, QMCLeafB.RunParamsSupply.runRadius] using h)

/-- The monomial round factor is what `RunParams.K` becomes. -/
theorem runParamsOfBound_K (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (B : ℕ) (hB1 : 1 ≤ B)
    (hB : Real.sqrt (QMCLeafB.RunParamsSupply.runM G : ℝ)
        * 8 * ((QMCLeafB.RunParamsSupply.runCAq G : ℝ) + 1)
        / (QMCLeafB.RunParamsSupply.runDq : ℝ) ≤ (2 : ℝ) ^ B) :
    (runParamsOfBound G hn B hB1 hB).K
      = (1 + G.n * G.n * B) * QMCLeafB.RunParamsSupply.runMcount G := rfl

/-! ## 4.  Axiom audit -/

#print axioms QMCLeafB.RoundCountBound.det_initShapeOf
#print axioms QMCLeafB.RoundCountBound.sqrt_inv_pow
#print axioms QMCLeafB.RoundCountBound.volPot_initShapeOf
#print axioms QMCLeafB.RoundCountBound.two_volPot_div_radius_pow
#print axioms QMCLeafB.RoundCountBound.simRounds_le_of_bound
#print axioms QMCLeafB.RoundCountBound.runParamsOfBound
#print axioms QMCLeafB.RoundCountBound.runParamsOfBound_K

end QMCLeafB.RoundCountBound


