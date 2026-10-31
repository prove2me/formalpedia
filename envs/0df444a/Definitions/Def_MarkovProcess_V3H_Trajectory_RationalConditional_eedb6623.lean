-- Prove2me | Definitions.Def_MarkovProcess_V3H_Trajectory_RationalConditional_eedb6623
-- name    : MarkovProcess_V3H_Trajectory_RationalConditional_eedb6623
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:13:19.382573+00:00
-- url     : https://prove2.me/theorems/212a336d-e1ea-4caa-8968-084a77b03d20
-- title:
--   MarkovProcess: MarkovProcess_V3H_Trajectory_RationalConditional_eedb6623
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_Trajectory_b0f7f66f
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_DenseFiltration_62a9879d
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Definitions.Def_MarkovProcess_V3H_Restart_RationalRestart_9d6a4f09
import Definitions.Def_MarkovProcess_V3H_Restart_RationalRestrictedRestart_3bd46ae7
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Definitions.Def_MarkovProcess_V3H_Trajectory_Basic_34bd0835
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinite

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Rational-time conditional Markov identities for the continuous trajectory

This file derives two local consequences of the rational joint restart law for the canonical
continuous-path trajectory.  First, restricting to any event in the canonical filtration and
then shifting at a rational time gives the path kernel restarted from the state at that time.
Second, every bounded strongly measurable functional of the shifted path satisfies the
corresponding conditional-expectation formula.

The times here are rational.  The strong Markov property at an arbitrary finite stopping time
is in `Trajectory/FellerStoppingRestart.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

private theorem continuousPathTrajectory_rationalJoint_apply
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (S : DenseTime) :
    ((continuousPathTrajectory P hP default) x).map (fun omega ↦
        (ContinuousPath.densePastRestriction S omega,
          ContinuousPath.shift (DenseTime.castOrderEmbedding S) omega)) =
      (((continuousPathTrajectory P hP default) x).map
          (ContinuousPath.densePastRestriction S)) ⊗ₘ
        Kernel.comap (continuousPathTrajectory P hP default)
          (ContinuousPath.densePastTerminal S)
          (ContinuousPath.measurable_densePastTerminal S) := by
  have h := congrArg (fun K : Kernel alpha
      ((Set.Iic S → alpha) × ContinuousPath alpha) ↦ K x)
    (_root_.MarkovProcess.SubMarkovKernelSemigroup.IsConservative.p2m_embedded_d5c36a7cc1744266
      P hP default hK S)
  change ((continuousPathTrajectory P hP default).map (fun omega ↦
      (ContinuousPath.densePastRestriction S omega,
        ContinuousPath.shift (DenseTime.castOrderEmbedding S) omega))) x =
    ContinuousPath.rationalPastFutureRestartKernel
      (continuousPathTrajectory P hP default) S x at h
  rw [Kernel.map_apply (continuousPathTrajectory P hP default)
      ((ContinuousPath.measurable_densePastRestriction S).prodMk
        (ContinuousPath.measurable_shift_fixed (DenseTime.castOrderEmbedding S))) x,
    ContinuousPath.rationalPastFutureRestartKernel_apply
      (continuousPathTrajectory P hP default) S x] at h
  exact h

/-- At a rational time, shifting the continuous trajectory after restriction to a past event is
the continuous path kernel restarted from the state at that time. -/
theorem continuousPathTrajectory_restrict_map_shift_denseTime
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (S : DenseTime) :
    ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := alpha)
        (DenseTime.castOrderEmbedding S)] A →
        (((continuousPathTrajectory P hP default) x).restrict A).map
            (ContinuousPath.shift (DenseTime.castOrderEmbedding S)) =
          Kernel.comap (continuousPathTrajectory P hP default)
              (ContinuousPath.coordinateProcess (alpha := alpha)
                (DenseTime.castOrderEmbedding S))
              (ContinuousPath.measurable_coordinateProcess
                (DenseTime.castOrderEmbedding S)) ∘ₘ
            (((continuousPathTrajectory P hP default) x).restrict A) := by
  exact _root_.MarkovProcess.ContinuousPath.p2m_embedded_cb0825700818b2e6
    (continuousPathTrajectory P hP default) x S
      (continuousPathTrajectory_rationalJoint_apply P hP default hK x S)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]



end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


