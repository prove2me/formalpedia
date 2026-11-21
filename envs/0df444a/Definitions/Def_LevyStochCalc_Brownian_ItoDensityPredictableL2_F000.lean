-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F000
-- name    : LevyStochCalc_Brownian_ItoDensityPredictableL2_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T12:52:46.40081+00:00
-- url     : https://prove2.me/theorems/29968c8c-e5b4-4396-9f09-a6b11070f8ca
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoDensityPredictableL2
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoDensityPredictableL2. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPointwise_F000
import Definitions.Def_SourceProof_8feb53937f8655328c047b33

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

/-- **Joint measurability of the predictable convergence set.** -/
private lemma predictable_convergence_set_measurable
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    MeasurableSet
      {p : Ω × ℝ | Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2))} := by
  have h_eq : {p : Ω × ℝ | Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2))}
      = {p : Ω × ℝ | Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1
          - g p.1 p.2)
        Filter.atTop (nhds 0)} := by
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using hp.sub h_const
    · intro hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using hp.add h_const
  rw [h_eq]
  have h_seq_meas : ∀ n, Measurable (fun (p : Ω × ℝ) =>
      (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1
        - g p.1 p.2) := by
    intro n
    have h_eval_meas : Measurable (fun p : Ω × ℝ =>
        (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
      unfold SimplePredictable.eval
      refine Finset.measurable_sum _ ?_
      intro i _
      refine Measurable.ite ?_ ?_ measurable_const
      · refine MeasurableSet.inter ?_ ?_
        · exact measurable_snd (measurableSet_Ioi
            (a := (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
              i.castSucc))
        · exact measurable_snd (measurableSet_Iic
            (a := (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
              i.succ))
      · exact (dyadicAvg_shifted_brownian_measurable T g h_meas n i).comp measurable_fst
    exact h_eval_meas.sub
      (h_meas.comp (by fun_prop : Measurable (fun (p : Ω × ℝ) => (p.1, p.2))))
  exact measurableSet_tendsto (nhds (0 : ℝ)) h_seq_meas
/-- **a.e. convergence on the product (predictable case).** -/
private lemma predictableDyadicSimple_brownian_ae_tendsto
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2)) := by
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
    (predictable_convergence_set_measurable hT g h_meas M h_bound)]
  refine Filter.Eventually.of_forall (fun ω => ?_)
  exact _root_.Prove2MeSourceProof.h_8feb53937f8655328c047b33 hT g h_meas M h_bound ω
-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.

end LevyStochCalc.Brownian.Ito


