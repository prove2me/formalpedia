-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F000
-- name    : LevyStochCalc_Poisson_CompensatedSimple_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:16:50.656965+00:00
-- url     : https://prove2.me/theorems/fe46036b-8e70-43d3-85f2-bd83b9ceedaa
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedSimple
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedSimple. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Compensated Poisson integral: simple predictable integrands

The simple predictable integrands `φ = ∑_i ξ_i · 1_{(t_i, t_{i+1}] × A_i}` and
their integral `simpleIntegral` against the compensated Poisson measure
`Ñ(dt, de) := N(dt, de) − ν(de) dt`, with the indicator/rectangle bookkeeping
lemmas. The moment identities are in `Poisson/CompensatedMoments.lean`; the
L²-isometry in `Poisson/CompensatedIsometry.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- A *simple predictable* integrand: a finite linear combination of
indicators on time-interval × measurable-set products. -/
structure SimplePredictable
    (Ω : Type u) [MeasurableSpace Ω]
    (E : Type v) [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν]
    (T : ℝ) where
  /-- Number of partition pieces. -/
  N : ℕ
  /-- Time-partition points `0 = t_0 < t_1 < ⋯ < t_N ≤ T`. -/
  partition : Fin (N + 1) → ℝ
  partition_zero : partition 0 = 0
  partition_le_T : partition (Fin.last N) ≤ T
  partition_strictMono : StrictMono partition
  /-- Mark sets `A_i ⊆ E`, each measurable with `ν(A_i) < ∞`. -/
  A : Fin N → Set E
  A_measurable : ∀ i : Fin N, MeasurableSet (A i)
  A_finite : ∀ i : Fin N, ν (A i) ≠ ⊤
  /-- Per-piece bounded coefficients `ξ_i : Ω → ℝ`. -/
  ξ : Fin N → Ω → ℝ
  ξ_bounded : ∀ i : Fin N, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M
  ξ_measurable : ∀ i : Fin N, Measurable (ξ i)
open Classical in
/-- Evaluate a simple predictable integrand at fixed `(s, e)`. -/
noncomputable def SimplePredictable.eval
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (s : ℝ) (e : E) (ω : Ω) : ℝ :=
  ∑ i : Fin φ.N,
    if φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ ∧ e ∈ φ.A i
    then φ.ξ i ω else 0
/-- The time-rectangle `(t_i ∧ t, t_{i+1} ∧ t] × A_i` for the `i`-th piece
of the partition, evaluated at running time `t`. -/
noncomputable def SimplePredictable.timeRect
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) (t : ℝ) : Set (ℝ × E) :=
  Set.Ioc (min (φ.partition i.castSucc) t) (min (φ.partition i.succ) t) ×ˢ φ.A i
/-- The full time-rectangle `(t_i, t_{i+1}] × A_i` (independent of cutoff). -/
noncomputable def SimplePredictable.fullRect
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) : Set (ℝ × E) :=
  Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ) ×ˢ φ.A i
end LevyStochCalc.Poisson.Compensated


