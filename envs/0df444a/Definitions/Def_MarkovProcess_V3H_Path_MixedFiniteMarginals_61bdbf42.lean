-- Prove2me | Definitions.Def_MarkovProcess_V3H_Path_MixedFiniteMarginals_61bdbf42
-- name    : MarkovProcess_V3H_Path_MixedFiniteMarginals_61bdbf42
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:02:23.771178+00:00
-- url     : https://prove2.me/theorems/d51cf303-7b10-4dad-b73f-c796e6155bbb
-- title:
--   MarkovProcess: MarkovProcess_V3H_Path_MixedFiniteMarginals_61bdbf42
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_Trajectory_b0f7f66f
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Restart_MixedPastFuture_e5e8ccdc
import Definitions.Def_MarkovProcess_V3H_Restart_MixedPastFuture_e5e8ccdc_PartA
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Definitions.Def_MarkovProcess_V3H_Trajectory_Basic_34bd0835
import Definitions.Def_MarkovProcess_V3H_Trajectory_FiniteMarginals_a8fbfae5
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
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
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
# Finite mixed past/future marginals of continuous trajectories

Every finite collection of rational coordinates drawn from the past through `S` and the shifted
future has the finite transition law on the corresponding union of absolute physical times,
followed by the canonical possibly noninjective coordinate pullback.  In particular, a terminal
past coordinate and a future coordinate at zero are both retained even though they observe the
same absolute time.

This is a finite-dimensional law identity.  The conditional factorization of that law through
the state at `S` is in `Restart/RationalRestart.lean`.
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

/-- A finite mixed rational past/shifted-future marginal is the finite transition law on its
absolute physical times, pulled back to the original mixed labels. -/
theorem p2m_embedded_4316e330caa9dd54
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (continuousPathTrajectory P hP default).map
        (I.restrict ∘ ContinuousPath.mixedPastShiftedCoordinates S) =
      (finiteSetKernel P (MixedPastFuture.absolutePhysicalFinset S I)).map
        (MixedPastFuture.pullbackAbsolutePhysical S I) := by
  let evaluateAbsolute : ContinuousPath alpha →
      MixedPastFuture.absolutePhysicalFinset S I → alpha :=
    fun path t ↦ path t
  have hEvaluateAbsolute : Measurable evaluateAbsolute := by
    rw [measurable_pi_iff]
    intro t
    exact ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  have hcoordinates :
      I.restrict ∘ ContinuousPath.mixedPastShiftedCoordinates S =
        MixedPastFuture.pullbackAbsolutePhysical S I ∘ evaluateAbsolute := by
    funext omega
    exact ContinuousPath.restrict_mixedPastShiftedCoordinates S I omega
  rw [hcoordinates, Kernel.map_comp_right]
  · change
      ((continuousPathTrajectory P hP default).map
        (fun path (t : denseTimePhysicalSet (MixedPastFuture.absoluteFinset S I)) ↦
          path t)).map (MixedPastFuture.pullbackAbsolutePhysical S I) = _
    rw [_root_.MarkovProcess.SubMarkovKernelSemigroup.IsConservative.p2m_embedded_b819d8df72e216cf P hP default hK]
    rfl
  · exact hEvaluateAbsolute
  · exact MixedPastFuture.measurable_pullbackAbsolutePhysical S I

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


