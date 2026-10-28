-- Prove2me | Definitions.Def_AvramDividend_Classical_BvFiniteGridClocks_ws01c
-- name    : AvramDividend_Classical_BvFiniteGridClocks_ws01c
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T13:06:21.843594+00:00
-- url     : https://prove2.me/theorems/2d81875c-9b5a-4bad-903c-074da5c0eaa7
-- title:
--   Finite first-below-barrier grid stopping-clock constructors in WithTop and NNReal
-- statement:
--   Defines the finite-list first strict downward barrier-observation clock, taking the minimum of observed crossing times with a finite fallback horizon, in both extended-nonnegative and genuinely finite nonnegative-real codomains. These are the exact reusable constructors needed to prove genuine finite stopping times and pass their future laws to the capped raw strict lower passage clock. The constructors are mathematically the same finite observation folds as in the WS1C research drafts.
-- source:
--   Merged declaration bodies exactly from work/avram_ws01c_binary_grid_stop_draft.lean and work/avram_ws01c_finite_clock_nnreal_adapter_draft.lean, marking the real-comparison constructors noncomputable because the strict real-order test is classically decidable.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.Classical

noncomputable def bv_finite_grid_below_clock_ws01c
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (H : ℝ≥0) (L : List ℝ≥0) : Ω → WithTop ℝ≥0 :=
  fun ω => L.foldr
    (fun t u => min
      (if Y t ω < b then (t : WithTop ℝ≥0) else (H : WithTop ℝ≥0)) u)
    (H : WithTop ℝ≥0)

noncomputable def bv_finite_grid_below_NNReal_ws01c
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (H : ℝ≥0) (L : List ℝ≥0) : Ω → ℝ≥0 :=
  fun ω =>
    L.foldr (fun t u => (if Y t ω < b then t else H) ⊓ u) H

end AvramDividend.Classical


