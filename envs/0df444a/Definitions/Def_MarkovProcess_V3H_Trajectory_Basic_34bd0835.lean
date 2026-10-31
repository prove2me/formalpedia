-- Prove2me | Definitions.Def_MarkovProcess_V3H_Trajectory_Basic_34bd0835
-- name    : MarkovProcess_V3H_Trajectory_Basic_34bd0835
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:54:21.215987+00:00
-- url     : https://prove2.me/theorems/3a80c14c-4a58-4d20-9110-ca5e557105e0
-- title:
--   MarkovProcess: MarkovProcess_V3H_Trajectory_Basic_34bd0835
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousLaw_cc004751
import Definitions.Def_MarkovProcess_V3H_Continuity_KolmogorovDenseTimeContinuousSupport_e9ca7f43
import Definitions.Def_MarkovProcess_V3H_DenseTime_PrefixKernel_a192bbea
import Definitions.Def_MarkovProcess_V3H_DenseTime_TrajectoryMarginals_db9e38cc
import Definitions.Def_MarkovProcess_V3H_DenseTime_Trajectory_b0f7f66f
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_Polish_87f91693
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
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
# Continuous-path trajectory kernels

This file transports the canonical dense-time trajectory of a conservative kernel semigroup to
continuous paths.  The explicit default is used only by the previously established measurable
extension away from the continuous-restriction range.  A coordinate Kolmogorov condition makes
that fallback irrelevant and transports the proved rational-time marginal identities.

No continuous-time Markov property, strong Markov property, Hunt-process assertion, or PDE
increment estimate is claimed.
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

/-- The canonical dense-time trajectory transported through the measurable continuous-extension
map.  Under the Kolmogorov hypothesis used below, its law is independent of `default`. -/
def continuousPathTrajectory (P : SubMarkovKernelSemigroup alpha)
    (hP : P.IsConservative) (default : ContinuousPath alpha) :
    Kernel alpha (ContinuousPath alpha) :=
  Kernel.toContinuousPathKernel
    (denseTimeTrajectory P hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding) default

/-- The transported continuous-path trajectory is a Markov kernel in its initial-state
parameter. -/
instance isMarkovKernel_continuousPathTrajectory
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha) :
    IsMarkovKernel (continuousPathTrajectory P hP default) := by
  unfold continuousPathTrajectory
  exact Kernel.isMarkovKernel_toContinuousPathKernel _ default



/-- Every rational-time evaluation of the continuous-path transport has the prescribed
semigroup marginal, provided the canonical dense-time coordinate process satisfies the
parameterwise Kolmogorov condition. -/
theorem p2m_embedded_dda797d33227c489
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (r : DenseTime) :
    (continuousPathTrajectory P hP default).map
        (fun path ↦ path (DenseTime.castOrderEmbedding r)) =
      P (DenseTime.castOrderEmbedding r) := by
  let kappa := denseTimeTrajectory P hP DenseTime.enumeration
    DenseTime.castOrderEmbedding.toEmbedding
  have hback :
      (continuousPathTrajectory P hP default).map ContinuousPath.denseRestriction = kappa := by
    exact Kernel.map_denseRestriction_toContinuousPathKernel_of_isKolmogorovCoordinate
      kappa default hK
  have hfun :
      (fun path : ContinuousPath alpha ↦ path (DenseTime.castOrderEmbedding r)) =
        (fun path : DenseTime → alpha ↦ path r) ∘ ContinuousPath.denseRestriction := by
    rfl
  rw [hfun, Kernel.map_comp_right]
  · rw [hback]
    exact _root_.MarkovProcess.SubMarkovKernelSemigroup.IsConservative.p2m_embedded_b6cde874390934be P hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding r
  · exact ContinuousPath.measurable_denseRestriction
  · exact measurable_pi_apply r

/-- Every finite enumeration-prefix marginal of the continuous-path transport is the already
constructed dense-time prefix law. -/
theorem p2m_embedded_364455a2d9664b7b
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (n : ℕ) :
    (continuousPathTrajectory P hP default).map
        (denseTimeTrajectoryPrefix DenseTime.enumeration n ∘
          ContinuousPath.denseRestriction) =
      denseTimePrefixKernel P DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n := by
  let kappa := denseTimeTrajectory P hP DenseTime.enumeration
    DenseTime.castOrderEmbedding.toEmbedding
  have hback :
      (continuousPathTrajectory P hP default).map ContinuousPath.denseRestriction = kappa := by
    exact Kernel.map_denseRestriction_toContinuousPathKernel_of_isKolmogorovCoordinate
      kappa default hK
  rw [Kernel.map_comp_right]
  · rw [hback]
    exact denseTimeTrajectory_map_prefix P hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding n
  · exact ContinuousPath.measurable_denseRestriction
  · exact measurable_denseTimeTrajectoryPrefix DenseTime.enumeration n

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


