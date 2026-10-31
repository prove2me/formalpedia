-- Prove2me | Definitions.Def_MarkovProcess_V3H_Time_FiniteDenseApproximationOrdered_4fc0c4f5
-- name    : MarkovProcess_V3H_Time_FiniteDenseApproximationOrdered_4fc0c4f5
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:59:18.836717+00:00
-- url     : https://prove2.me/theorems/337c78d0-708d-4613-a2a8-09dae4da6c69
-- title:
--   MarkovProcess: MarkovProcess_V3H_Time_FiniteDenseApproximationOrdered_4fc0c4f5
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Definitions.Def_MarkovProcess_V3H_Time_FiniteOrderedTimes_717796dd
import Definitions.Def_MarkovProcess_V3H_Trajectory_AllTimeFiniteMarginals_51403fc5
import Definitions.Def_MarkovProcess_V3H_Trajectory_FiniteMarginals_a8fbfae5
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

@[simp]
theorem p2m_embedded_8a504eab75f49bef {I : Finset NNReal}
    (q : I ↪o DenseTime) (i : Fin I.card) :
    finiteDenseApproximationOrderedTimes q i =
      DenseTime.castOrderEmbedding (q (I.orderIsoOfFin rfl i)) :=
  rfl

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


