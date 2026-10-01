-- Prove2me | Definitions.Def_Yukon_8321510fb5e60b1f0f309da5
-- name    : Yukon_8321510fb5e60b1f0f309da5
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:38:21.237665+00:00
-- url     : https://prove2.me/theorems/afcb6cd3-23c3-4a47-9842-5685fbccc203
-- title:
--   YukonModule.ToMathlib.Analysis.MeanInequalities.part0
-- statement:
--   Source module ToMathlib.Analysis.MeanInequalities.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/ToMathlib/Analysis/MeanInequalities.lean
--
--   provider-v8:e61d58b504a2fbdb724420bd6723c049e55a8e52369e15220a08fce0bc2aca40
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODplNjFkNThiNTA0YTJmYmRiNzI0NDIwYmQ2NzIzYzA0OWU1NWE4ZTUyMzY5ZTE1MjIwYTA4ZmNlMGJjMmFjYTQwIiwiaGFzaCI6ImI5MTFhMWY0YmY5MDg2ZWIwODM5ZTFlZmE1ZjU5YTgwYzMyYzAzN2QyMDEwYjA2YTM0MGVhNDY2MmNiNzdmMDkiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uXzgzMjE1MTBmYjVlNjBiMWYwZjMwOWRhNSIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable


public import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# Hölder Inequality for ENNReal-Valued Infinite Sums

This file provides a `tsum` version of Hölder's inequality for `ℝ≥0∞`-valued functions,
obtained by specializing the `lintegral` Hölder inequality to the counting measure.

The main advantage over `NNReal.inner_le_Lp_mul_Lq_tsum` in Mathlib is that no
`Summable` hypotheses are needed: `ℝ≥0∞` sums always converge (to `⊤` in the worst case).

## Main Results

- `ENNReal.inner_le_Lp_mul_Lq_tsum`: Hölder's inequality for `ℝ≥0∞`-valued `tsum`.
-/

@[expose] public section


noncomputable section

open MeasureTheory ENNReal

namespace ENNReal

variable {ι : Type*}

/-- Hölder's inequality for `ℝ≥0∞`-valued infinite sums:
`∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1/p) * (∑' i, g i ^ q) ^ (1/q)`.

Obtained by specializing `ENNReal.lintegral_mul_le_Lp_mul_Lq` to the counting measure
with `DiscreteMeasurableSpace`. No `Summable` hypotheses are needed. -/
theorem inner_le_Lp_mul_Lq_tsum {p q : ℝ} (hpq : p.HolderConjugate q)
    (f g : ι → ℝ≥0∞) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  letI : MeasurableSpace ι := ⊤
  haveI : DiscreteMeasurableSpace ι := ⟨fun _ => trivial⟩
  have := lintegral_mul_le_Lp_mul_Lq (α := ι) Measure.count hpq
    (AEMeasurable.of_discrete (f := f)) (AEMeasurable.of_discrete (f := g))
  simp only [lintegral_count, Pi.mul_apply] at this
  exact this

end ENNReal


