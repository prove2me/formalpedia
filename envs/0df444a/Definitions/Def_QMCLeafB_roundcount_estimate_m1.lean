-- Prove2me | Definitions.Def_QMCLeafB_roundcount_estimate_m1
-- name    : QMCLeafB_roundcount_estimate_m1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:40:21.119342+00:00
-- url     : https://prove2.me/theorems/75e438df-e2e8-41f4-a1c0-1291987fcea8
-- title:
--   QMCLeafB roundcount_estimate_m1
-- statement:
--   # leaf B phase 13 — `roundcount-estimate` (swarm `smw17fqzz`, member m1, direction d6)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_budget_bound_m1
import Definitions.Def_QMCLeafB_hspec_m4
/-
# leaf B phase 13 — `roundcount-estimate` (swarm `smw17fqzz`, member m1, direction d6)

**The estimate `Check_hspec_m4` §3j explicitly leaves open.**  Its own header says:

> The estimate `budgetRounds ≤ C (n+1)^d · bitCost (Rq G)` is *not* here: it is the
> `Nat.clog`/`Real.log` brick.

This file is that brick, and nothing else: it composes

* `BudgetBound.budgetRounds_le_log` (mine) —
  `budgetRounds G 1 m ≤ m·(n²+1)·(Nat.clog 2 (⌈Rq G⌉+1) + n + 8)`;
* `Rq_add_one_le_two_pow_bitCost` (m4) — `Rq G + 1 ≤ 2 ^ bitCost (Rq G)`;
* `bitCost_Rq_le` (m4) — `bitCost (Rq G) ≤ 48·(encodeInput G).length + 16`,

into the two shapes a fuel needs:

* `budgetRounds_le_bitCost` — `budgetRounds G 1 m ≤ m·(n+1)²·(bitCost (Rq G) + n + 10)`;
* `budgetRounds_le_input_length` — `budgetRounds G 1 m ≤ 80·m·(n+1)³·(L+1)³` at
  `L = (encodeInput G).length`, i.e. a monomial in the dimension and the input length.

Together with m4's `poly_bitCostRq` (`bitCost (Rq G)` is a `Poly` function of the request) this closes
the arithmetic of the fuel slot: the fuel length may be taken to be
`T p := 80·m·(n+1)³·(L+1)³` with `L = (encodeRequest p.1).length`, and `monomial_mul_le_seed_pow`
absorbs it once the seed is padded by a constant.

No `sorry`, no `axiom`; audits at the end.
-/

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.RoundCountEstimate

open QuantumMaxCutEnergy

/-- **`⌈Rq⌉+1` is under `2^(bitCost+1)`**, hence `Nat.clog 2 (⌈Rq⌉+1) ≤ bitCost + 1`. -/
theorem clog_ceil_Rq_le (G : QuantumMaxCutEnergy.Input) :
    Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1)
      ≤ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1 := by
  refine (Nat.clog_le_iff_le_pow (by norm_num)).mpr ?_
  have hpow : QMCLeafB.EngineRuntime.Rq G ≤ (2 : ℚ) ^ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) := by
    have h := QMCLeafB.Hspec.Rq_add_one_le_two_pow_bitCost G
    linarith
  have hceil : Nat.ceil (QMCLeafB.EngineRuntime.Rq G)
      ≤ 2 ^ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) := by
    refine Nat.ceil_le.mpr ?_
    have hcast : ((2 : ℚ) ^ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) : ℚ)
        = (((2 : ℕ) ^ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) : ℕ) : ℚ) := by
      push_cast
      ring
    calc QMCLeafB.EngineRuntime.Rq G
        ≤ ((2 : ℚ) ^ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G)) := hpow
      _ = (((2 : ℕ) ^ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) : ℕ) : ℚ) := hcast
  refine le_trans (Nat.add_le_add_right hceil 1) ?_
  have ht : (1 : ℕ) ≤ 2 ^ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) := Nat.one_le_two_pow
  have h2 : 2 ^ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1
      ≤ 2 ^ (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1) := by
    rw [pow_succ]
    omega
  exact h2

/-- **The estimate in `bitCost` form.** -/
theorem budgetRounds_le_bitCost (G : QuantumMaxCutEnergy.Input) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G 1 m
      ≤ m * ((G.n + 1) ^ 2
          * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 10)) := by
  refine le_trans (QMCLeafB.BudgetBound.budgetRounds_le_log G m) ?_
  refine Nat.mul_le_mul_left m ?_
  have hc := clog_ceil_Rq_le G
  have h1 : G.n * G.n + 1 ≤ (G.n + 1) ^ 2 := by nlinarith
  have h2 : Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n + 8
      ≤ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 10 := by omega
  exact Nat.mul_le_mul h1 h2

/-- **The estimate in input-length form**: a monomial in the dimension and `L = (encodeInput G).length`. -/
theorem budgetRounds_le_input_length (G : QuantumMaxCutEnergy.Input) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G 1 m
      ≤ 80 * m * ((G.n + 1) ^ 3 * ((encodeInput G).length + 1) ^ 3) := by
  set L := (encodeInput G).length with hL
  have hbc : QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) ≤ 48 * L + 16 :=
    QMCLeafB.Hspec.bitCost_Rq_le G
  refine le_trans (budgetRounds_le_bitCost G m) ?_
  -- `(n+1)²·(bitCost + n + 10) ≤ 80·(n+1)³·(L+1)³`
  have hkey : (G.n + 1) ^ 2 * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 10)
      ≤ (G.n + 1) ^ 2 * (48 * L + 16 + G.n + 10) := by
    apply Nat.mul_le_mul_left
    omega
  refine le_trans (Nat.mul_le_mul_left m hkey) ?_
  -- absorb the constants, using the unary prefix `G.n ≤ L`
  have hnL : G.n ≤ L := by
    rw [hL]
    simp only [encodeInput, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    omega
  have hL3 : L ≤ (L + 1) ^ 3 := by
    have hpos : (0 : ℕ) < (L + 1) ^ 2 := by positivity
    have h1 : (L + 1) ≤ (L + 1) ^ 3 := by
      calc (L + 1) = (L + 1) * 1 := by ring
        _ ≤ (L + 1) * (L + 1) ^ 2 := Nat.mul_le_mul_left _ (by omega)
        _ = (L + 1) ^ 3 := by ring
    omega
  have hX : 48 * L + 16 + G.n + 10 ≤ 75 * (L + 1) ^ 3 := by
    have h1 : 48 * L ≤ 48 * (L + 1) ^ 3 := Nat.mul_le_mul_left 48 hL3
    have h2 : G.n ≤ (L + 1) ^ 3 := le_trans hnL hL3
    have h3 : (1 : ℕ) ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hsq : (G.n + 1) ^ 2 ≤ (G.n + 1) ^ 3 := by
    have h0 : (0 : ℕ) < (G.n + 1) := by omega
    calc (G.n + 1) ^ 2 = (G.n + 1) ^ 2 * 1 := by ring
      _ ≤ (G.n + 1) ^ 2 * (G.n + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (G.n + 1) ^ 3 := by ring
  refine le_trans (Nat.mul_le_mul_left m (Nat.mul_le_mul hsq hX)) ?_
  have h75 : m * ((G.n + 1) ^ 3 * (75 * (L + 1) ^ 3))
      ≤ 80 * m * ((G.n + 1) ^ 3 * (L + 1) ^ 3) := by
    have : m * ((G.n + 1) ^ 3 * (75 * (L + 1) ^ 3))
        = 75 * (m * ((G.n + 1) ^ 3 * (L + 1) ^ 3)) := by ring
    rw [this]
    have : 75 * (m * ((G.n + 1) ^ 3 * (L + 1) ^ 3))
        ≤ 80 * (m * ((G.n + 1) ^ 3 * (L + 1) ^ 3)) :=
      Nat.mul_le_mul_right _ (by norm_num)
    calc 75 * (m * ((G.n + 1) ^ 3 * (L + 1) ^ 3))
        ≤ 80 * (m * ((G.n + 1) ^ 3 * (L + 1) ^ 3)) := this
      _ = 80 * m * ((G.n + 1) ^ 3 * (L + 1) ^ 3) := by ring
  exact h75

end QMCLeafB.RoundCountEstimate

/-! ## Axiom audit -/

#print axioms QMCLeafB.RoundCountEstimate.clog_ceil_Rq_le
#print axioms QMCLeafB.RoundCountEstimate.budgetRounds_le_bitCost
#print axioms QMCLeafB.RoundCountEstimate.budgetRounds_le_input_length


