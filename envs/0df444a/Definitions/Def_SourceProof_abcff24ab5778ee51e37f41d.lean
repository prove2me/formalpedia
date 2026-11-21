-- Prove2me | Definitions.Def_SourceProof_abcff24ab5778ee51e37f41d
-- name    : SourceProof_abcff24ab5778ee51e37f41d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:51:50.175381+00:00
-- url     : https://prove2.me/theorems/d3d46040-f7a4-4159-8960-c3f2b5fd6004
-- title:
--   LevyStochCalc source module: SourceProof_abcff24ab5778ee51e37f41d
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.stronglyMeasurable_partialSum` comes from the `LevyStochCalc.Brownian.ItoFourthMomentIncrements` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F001

open private stronglyMeasurable_range_sum from Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F001
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of a Brownian increment and the partial sums of the elementary integral

The moments of a centred real Gaussian and of a Brownian increment: they scale with the standard
deviation, the odd ones vanish, and a random variable measurable before the increment factors out
of the integral against any power of it. On top of this the elementary integral of a simple
integrand is presented as the partial sums `SimplePredictable.partialSum` of its summands, with
their measurability, adaptedness and `Lᵖ` membership, and the variance budget
`SimplePredictable.varClock c k = ∑_{j < k} c_j² (τ_{j+1} − τ_j)` of a per-tile coefficient
bound `c`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section Increments

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

end Increments

namespace SimplePredictable

variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

theorem _root_.Prove2MeSourceProof.h_abcff24ab5778ee51e37f41d (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {k : ℕ} (hk : k ≤ G.N) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition ⟨k, by omega⟩)) (G.partialSum W k) := by
  refine stronglyMeasurable_range_sum fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hiN : i < G.N := lt_of_lt_of_le hi hk
  have hterm : (LevyStochCalc.Brownian.Ito.SimplePredictable.term G) W i = fun ω => G.ξ ⟨i, hiN⟩ ω
      * (W.W (G.partition (⟨i, hiN⟩ : Fin G.N).succ) ω
        - W.W (G.partition (⟨i, hiN⟩ : Fin G.N).castSucc) ω) := by
    funext ω; rw [LevyStochCalc.Brownian.Ito.SimplePredictable.term, dif_pos hiN]
  rw [hterm]
  have hle1 : G.partition (⟨i, hiN⟩ : Fin G.N).castSucc
      ≤ G.partition (⟨k, by omega⟩ : Fin (G.N + 1)) :=
    G.partition_strictMono.monotone (by rw [Fin.le_def]; simp [Fin.castSucc]; omega)
  have hle2 : G.partition (⟨i, hiN⟩ : Fin G.N).succ
      ≤ G.partition (⟨k, by omega⟩ : Fin (G.N + 1)) :=
    G.partition_strictMono.monotone (by rw [Fin.le_def]; simp [Fin.succ]; omega)
  exact ((h_adapt ⟨i, hiN⟩).mono (ℱ.mono hle1)).mul
    (((hℱ.measurable _).stronglyMeasurable.mono (ℱ.mono hle2)).sub
      ((hℱ.measurable _).stronglyMeasurable.mono (ℱ.mono hle1)))
end SimplePredictable

end LevyStochCalc.Brownian.Ito


