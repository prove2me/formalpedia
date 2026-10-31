-- Prove2me | Definitions.Def_MarkovProcess_V3H_Path_ShiftCompactTestConvergence_fc2b2de1
-- name    : MarkovProcess_V3H_Path_ShiftCompactTestConvergence_fc2b2de1
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:58:24.459007+00:00
-- url     : https://prove2.me/theorems/3ab489d7-8bb2-4b7f-bfe1-369ea93fb3f1
-- title:
--   MarkovProcess: MarkovProcess_V3H_Path_ShiftCompactTestConvergence_fc2b2de1
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Definitions.Def_MarkovProcess_V3H_Trajectory_AllTimeFiniteMarginals_51403fc5
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dominated convergence for shifted continuous-path tests

This file records path-side dominated-convergence tools for deterministic times approached by
dense times. The measure is any finite measure on continuous-path space; no Markov or kernel
assumption is used.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty CompactlySupported

namespace MarkovProcess

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [LocallyCompactSpace alpha]

omit [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] in
/-- Integrals of a bounded continuous state observable along convergent continuous-path
coordinates converge under any finite path measure. -/
theorem tendsto_integral_continuousPath_eval_of_tendsto
    (mu : Measure (ContinuousPath alpha)) [IsFiniteMeasure mu]
    (s : NNReal) (q : ℕ → DenseTime)
    (hq : Tendsto (fun n ↦ DenseTime.castOrderEmbedding (q n)) atTop (nhds s))
    (g : alpha → ℝ) (hg : Continuous g) (C : ℝ)
    (hgC : ∀ y, ‖g y‖ ≤ C) :
    Tendsto
      (fun n ↦ ∫ omega, g (omega (DenseTime.castOrderEmbedding (q n))) ∂mu)
      atTop (nhds (∫ omega, g (omega s) ∂mu)) := by
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [] with n
    exact (hg.comp (ContinuousPath.continuous_eval (alpha := alpha)
      (DenseTime.castOrderEmbedding (q n)))).aestronglyMeasurable
  · exact ⟨C, Filter.Eventually.of_forall fun n ↦ ae_of_all _ fun omega ↦
      hgC (omega (DenseTime.castOrderEmbedding (q n)))⟩
  · filter_upwards [] with omega
    exact hg.continuousAt.tendsto.comp
      (omega.continuous.continuousAt.tendsto.comp hq)

omit [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] in
/-- Compact-test integrals of finitely many relative dense-time coordinates converge when the
deterministic shift times converge. The finite coordinate set may be empty. -/
theorem p2m_embedded_f20777638aaa0c79
    (mu : Measure (ContinuousPath alpha)) [IsFiniteMeasure mu]
    (s : NNReal) (q : ℕ → DenseTime)
    (hq : Tendsto (fun n ↦ DenseTime.castOrderEmbedding (q n)) atTop (nhds s))
    (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    Tendsto
      (fun n ↦ ∫ omega, f (fun j : J ↦
        omega (DenseTime.castOrderEmbedding (q n) +
          DenseTime.castOrderEmbedding j)) ∂mu)
      atTop
      (nhds (∫ omega, f (fun j : J ↦
        omega (s + DenseTime.castOrderEmbedding j)) ∂mu)) := by
  let f₀ : C₀(J → alpha, ℝ) :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [] with n
    exact (f.continuous.comp (ContinuousPath.continuous_finiteEvaluation
      (fun j : J ↦ DenseTime.castOrderEmbedding (q n) +
        DenseTime.castOrderEmbedding j))).aestronglyMeasurable
  · refine ⟨‖f₀‖, Filter.Eventually.of_forall fun n ↦ ?_⟩
    filter_upwards [] with omega
    simpa only [f₀, PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply,
      Real.norm_eq_abs] using! f₀.toBCF.norm_coe_le_norm
      (fun j : J ↦ omega (DenseTime.castOrderEmbedding (q n) +
        DenseTime.castOrderEmbedding j))
  · filter_upwards [] with omega
    apply f.continuous.continuousAt.tendsto.comp
    rw [tendsto_pi_nhds]
    intro j
    exact omega.continuous.continuousAt.tendsto.comp
      (hq.add tendsto_const_nhds)

end
end MarkovProcess


