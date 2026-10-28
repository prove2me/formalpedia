-- Prove2me | Definitions.Def_MarkovProcess_Time_FiniteDenseApproximationOrdered
-- name    : MarkovProcess_Time_FiniteDenseApproximationOrdered
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T13:36:16.90099+00:00
-- url     : https://prove2.me/theorems/4a51f008-59a5-4b3d-a998-577ea85778d8
-- title:
--   MarkovProcess definitions: Time.FiniteDenseApproximationOrdered
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Time.FiniteDenseApproximationOrdered`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Time/FiniteDenseApproximationOrdered.lean#L1-L118

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousExtension
import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousLaw
import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Continuity_GlobalDyadicFloorModification
import Definitions.Def_MarkovProcess_Continuity_KolmogorovTimeShift
import Definitions.Def_MarkovProcess_Continuity_ShiftedUnitModification
import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
import Definitions.Def_MarkovProcess_DenseTime_Trajectory
import Definitions.Def_MarkovProcess_Feller_Semigroup
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_C0_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_Integral_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_PositiveC0OperatorMeasure
import Definitions.Def_MarkovProcess_Path_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Path_Polish_SourceClosedV3
import Definitions.Def_MarkovProcess_Semigroup_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Definitions.Def_MarkovProcess_Trajectory_AllTimeFiniteMarginals
import Definitions.Def_MarkovProcess_Trajectory_Basic
import Definitions.Def_MarkovProcess_Trajectory_FiniteMarginals
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

/-!
# Ordered form of finite dense approximations

This file expresses a finite dense-approximation kernel as a finite-time kernel at its
increasing physical times. The final coordinate reindexing is the fixed map
`orderedPathToFiniteSet I`; it does not depend on the chosen dense approximation `q`.

The construction also covers `I = ∅`. In that case the ordered time family and both path
coordinate types are empty.
-/

open MeasureTheory ProbabilityTheory Topology Filter
open scoped NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

/-- The physical times of a finite dense approximation, listed in the increasing order inherited
from the original finite set. For an empty finite set this is the empty ordered family. -/
def finiteDenseApproximationOrderedTimes {I : Finset NNReal} (q : I ↪o DenseTime) :
    FiniteOrderedTimes I.card :=
  ((I.orderIsoOfFin rfl).toOrderEmbedding.trans q).trans DenseTime.castOrderEmbedding



private theorem approximation_mem {I : Finset NNReal} (q : I ↪o DenseTime) (t : I) :
    DenseTime.castOrderEmbedding (q t) ∈ finiteDenseApproximationPhysicalSet q := by
  rw [finiteDenseApproximationPhysicalSet, denseTimePhysicalSet, Finset.mem_map]
  refine ⟨q t, ?_, rfl⟩
  rw [finiteDenseApproximationIndexSet, Finset.mem_map]
  exact ⟨t, Finset.mem_univ t, rfl⟩

private def finiteDenseApproximationOrderEmb {I : Finset NNReal} (q : I ↪o DenseTime) :
    Fin I.card ↪o Fin (finiteDenseApproximationPhysicalSet q).card :=
  (I.orderIsoOfFin rfl).toOrderEmbedding |>.trans
    (OrderEmbedding.ofStrictMono
      (fun t : I => (⟨DenseTime.castOrderEmbedding (q t), approximation_mem q t⟩ :
        finiteDenseApproximationPhysicalSet q))
        (fun _ _ h => DenseTime.castOrderEmbedding.strictMono (q.strictMono h))) |>.trans
    ((finiteDenseApproximationPhysicalSet q).orderIsoOfFin rfl).symm.toOrderEmbedding









end

end MarkovProcess.SubMarkovKernelSemigroup


