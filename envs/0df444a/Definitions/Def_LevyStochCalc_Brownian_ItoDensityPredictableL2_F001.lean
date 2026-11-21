-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F001
-- name    : LevyStochCalc_Brownian_ItoDensityPredictableL2_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:42:19.560916+00:00
-- url     : https://prove2.me/theorems/58a46c32-6132-4538-a4f7-4ef684b6d968
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoDensityPredictableL2
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoDensityPredictableL2. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPointwise_F000
import Definitions.Def_SourceProof_5731c142c22a48f56440eba3
import Definitions.Def_SourceProof_9fe041c50928f190f90f5621

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# `L²` convergence of the predictable dyadic approximations

For a bounded jointly measurable integrand the left-shifted dyadic simple processes
converge to it in `L²(Ω × [0,T])`, giving density of the simple predictable processes and
of the adapted simple processes in the bounded case, joint measurability of the evaluation
map and the `L²` Cauchy property of the approximating sequence.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Step 4 (chain assembly):** Bounded measurable functions are L²-approximable
by `SimplePredictable`. Direct construction via `dyadicSimplePredictable_brownian`. -/
lemma simplePredictable_dense_L2_bounded_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖g ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (nhds 0) :=
  ⟨fun n => dyadicSimplePredictable_brownian hT g h_meas M h_bound n,
   _root_.Prove2MeSourceProof.h_9fe041c50928f190f90f5621 hT g h_meas M h_bound⟩
/-- **Adapted bounded density (Brownian).** Bounded progressively measurable
functions are L²-approximable by ADAPTED `SimplePredictable`s.

Construction via `predictableDyadicSimple_brownian` (the left-shifted dyadic
average), which is `ℱ_{t_i}`-StronglyMeasurable for progressively measurable `g`. -/
lemma adaptedSimple_dense_L2_bounded_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ g)
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      (∀ n : ℕ, ∀ i : Fin (Hn n).N,
        @MeasureTheory.StronglyMeasurable Ω ℝ _
          (ℱ ((Hn n).partition i.castSucc)) ((Hn n).ξ i)) ∧
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖g ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (nhds 0) :=
  ⟨fun n => predictableDyadicSimple_brownian hT g h_meas M h_bound n,
   fun n i => predictableDyadicSimple_brownian_adapted ℱ hT g h_meas M h_bound
     h_progMeas n i,
   _root_.Prove2MeSourceProof.h_5731c142c22a48f56440eba3 hT g h_meas M h_bound⟩
/-- **Partition endpoint of `predictableDyadicSimple_brownian` is T.** Trivially
inherited from `dyadicPartition_brownian_last`. -/
lemma predictableDyadicSimple_brownian_partition_last
    {T : ℝ} (hT : 0 < T) (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) :
    (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
      (Fin.last (predictableDyadicSimple_brownian hT g h_meas M h_bound n).N)
      = T := by
  change dyadicPartition_brownian T n (Fin.last (2 ^ n)) = T
  exact dyadicPartition_brownian_last T n
-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.

end LevyStochCalc.Brownian.Ito


