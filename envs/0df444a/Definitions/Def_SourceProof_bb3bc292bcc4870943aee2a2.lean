-- Prove2me | Definitions.Def_SourceProof_bb3bc292bcc4870943aee2a2
-- name    : SourceProof_bb3bc292bcc4870943aee2a2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:45:04.462195+00:00
-- url     : https://prove2.me/theorems/99399f41-bec7-4ef0-8e7d-7e9e6dc1cc47
-- title:
--   LevyStochCalc source module: SourceProof_bb3bc292bcc4870943aee2a2
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.progressivelyMeasurable_globalPatch` comes from the `LevyStochCalc.Ito.PicardGlobal` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardGlobal_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From window solutions to a solution on `[0, ∞)`

The Bielecki contraction produces a solution on each finite window. Uniqueness on the shorter of
two windows makes the family consistent, and right-continuity upgrades that to an almost-sure
agreement of whole paths, so the windows can be glued along `⌈t⌉₊` into a single path map that
restricts to a window solution on every `[0, T]`.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### Right-continuity upgrades per-time equality to path equality -/

/-! ### The glued path map -/

omit [MeasurableSpace E] [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_bb3bc292bcc4870943aee2a2
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hY : ∀ k, ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y k s ω i)
    (i : Fin n) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => globalPatch Y s ω i := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hsum : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => LevyStochCalc.Ito.Picard.globalPatch Y s p.1 i) p.2)
      = ∑ k ∈ Finset.range (⌈t⌉₊ + 1),
          (fun p : Ω × ℝ => Set.indicator {q : Ω × ℝ | ⌈q.2⌉₊ = k}
            (fun q : Ω × ℝ => (Set.Iic t).indicator (fun s => Y k s q.1 i) q.2) p) := by
    funext p
    rw [Finset.sum_apply]
    by_cases hp : p.2 ≤ t
    · have hmem : ⌈p.2⌉₊ ∈ Finset.range (⌈t⌉₊ + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.ceil_mono hp))
      rw [Finset.sum_eq_single_of_mem ⌈p.2⌉₊ hmem]
      · rw [Set.indicator_of_mem (by simp : p ∈ {q : Ω × ℝ | ⌈q.2⌉₊ = ⌈p.2⌉₊})]
        simp [Set.indicator_of_mem (Set.mem_Iic.mpr hp), LevyStochCalc.Ito.Picard.globalPatch]
      · intro b _ hb
        exact Set.indicator_of_notMem (by simpa [eq_comm] using hb) _
    · rw [Set.indicator_of_notMem (by simpa using hp)]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      by_cases hq : p ∈ {q : Ω × ℝ | ⌈q.2⌉₊ = k}
      · rw [Set.indicator_of_mem hq, Set.indicator_of_notMem (by simpa using hp)]
      · exact Set.indicator_of_notMem hq _
  have hterm : ∀ k : ℕ, StronglyMeasurable
      (fun p : Ω × ℝ => Set.indicator {q : Ω × ℝ | ⌈q.2⌉₊ = k}
        (fun q : Ω × ℝ => (Set.Iic t).indicator (fun s => Y k s q.1 i) q.2) p) := fun k =>
    (hY k i t).indicator
      ((measurable_snd (α := Ω) (β := ℝ)).nat_ceil (measurableSet_singleton k))
  rw [hsum]
  exact Finset.stronglyMeasurable_sum _ fun k _ => hterm k
/-! ### Consistency of a family of window solutions -/

section Glue

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)

end Glue

end LevyStochCalc.Ito.Picard


