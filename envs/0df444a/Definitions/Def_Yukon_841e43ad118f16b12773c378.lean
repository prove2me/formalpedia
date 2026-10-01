-- Prove2me | Definitions.Def_Yukon_841e43ad118f16b12773c378
-- name    : Yukon_841e43ad118f16b12773c378
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:38:16.485152+00:00
-- url     : https://prove2.me/theorems/1ac24b78-3ac3-4f9f-8056-4dd08924d0d1
-- title:
--   YukonModule.ToMathlib.Probability.ProbabilityMassFunction.TailSums.part0
-- statement:
--   Source module ToMathlib.Probability.ProbabilityMassFunction.TailSums.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/ToMathlib/Probability/ProbabilityMassFunction/TailSums.lean
--
--   provider-v8:974fe644add444b1c4b1ffcc1ad70f3efd83f88bfc47789387e64f5a62d38b13
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODo5NzRmZTY0NGFkZDQ0NGIxYzRiMWZmY2MxYWQ3MGYzZWZkODNmODhiZmM0Nzc4OTM4N2U2NGY1YTYyZDM4YjEzIiwiaGFzaCI6ImQ5NjdjOGM4NDdiNTdiZTc2ODI5NTRlNTM0ZDg0ZmJjMDkyYWQ0YzM4ZjRlY2YwYWU5NzU3MDY3YTg5Mjc2OWMiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uXzg0MWU0M2FkMTE4ZjE2YjEyNzczYzM3OCIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal


public import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# Tail-Sum Identities for `PMF`

This file records discrete tail-sum formulas for nonnegative `ℕ`-valued random variables.

The core identity is the standard discrete expectation formula

`E[X] = ∑ i, Pr[i < X]`

for `ℕ`-valued random variables with values in `ℝ≥0∞`.

We first prove the corresponding summation identity for arbitrary nonnegative sequences, and then
specialize it to probability mass functions.
-/

@[expose] public section

open scoped ENNReal

namespace ENNReal

/-- Tail-sum identity for a nonnegative sequence on `ℕ`:

`∑' n, f n * n = ∑' i, ∑' n, if i < n then f n else 0`.

This is the discrete nonnegative analogue of writing `n = ∑_{i < n} 1` and exchanging the order of
summation. -/
theorem tsum_mul_nat_eq_tsum_tail (f : ℕ → ℝ≥0∞) :
    (∑' n : ℕ, f n * (n : ℝ≥0∞)) = ∑' i : ℕ, ∑' n : ℕ, if i < n then f n else 0 := by
  calc
    ∑' n : ℕ, f n * (n : ℝ≥0∞) = ∑' n : ℕ, (n : ℝ≥0∞) * f n := by
      refine tsum_congr fun n => ?_
      rw [mul_comm]
    _ = ∑' n : ℕ, ∑' i : ℕ, if i < n then f n else 0 := by
      refine tsum_congr fun n => ?_
      rw [tsum_eq_sum (s := Finset.range n)]
      · have hsum :
            ∑ b ∈ Finset.range n, (if b < n then f n else 0) =
              ∑ _b ∈ Finset.range n, f n := by
              refine Finset.sum_congr rfl ?_
              intro b hb
              simp [Finset.mem_range.mp hb]
        rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
      · intro i hi
        simp only [Finset.mem_range] at hi
        simp [if_neg hi]
    _ = ∑' i : ℕ, ∑' n : ℕ, if i < n then f n else 0 := ENNReal.tsum_comm

end ENNReal

namespace PMF

/-- Tail-sum identity for the `ℝ≥0∞`-valued expectation of a `PMF ℕ`:

`∑' n, p n * n = ∑' i, p.toMeasure {n | i < n}`.

This is the discrete formula `E[X] = ∑ i, Pr[i < X]` for `ℕ`-valued random variables. -/
theorem tsum_coe_mul_nat_eq_tsum_measure_Ioi (p : PMF ℕ) :
    (∑' n : ℕ, p n * (n : ℝ≥0∞)) = ∑' i : ℕ, p.toMeasure (Set.Ioi i) := by
  calc
    ∑' n : ℕ, p n * (n : ℝ≥0∞) = ∑' i : ℕ, ∑' n : ℕ, if i < n then p n else 0 :=
      ENNReal.tsum_mul_nat_eq_tsum_tail p
    _ = ∑' i : ℕ, p.toMeasure (Set.Ioi i) := by
      refine tsum_congr fun i => ?_
      rw [p.toMeasure_apply_eq_tsum]
      refine tsum_congr fun n => ?_
      by_cases h : i < n <;> simp [Set.Ioi, Set.indicator, h]

/-- Tail domination bounds the `ℝ≥0∞`-valued expectation of a `PMF ℕ`.

If each tail probability `Pr[i < X]` is bounded above by `a i`, then
`E[X] ≤ ∑ i, a i`. This is the generic discrete upper-bound principle used to turn
tail estimates into expectation bounds. -/
theorem tsum_coe_mul_nat_le_tsum_of_measure_Ioi_le (p : PMF ℕ) {a : ℕ → ℝ≥0∞}
    (h : ∀ i : ℕ, p.toMeasure (Set.Ioi i) ≤ a i) :
    (∑' n : ℕ, p n * (n : ℝ≥0∞)) ≤ ∑' i : ℕ, a i := by
  rw [tsum_coe_mul_nat_eq_tsum_measure_Ioi]
  exact ENNReal.tsum_le_tsum h

end PMF


