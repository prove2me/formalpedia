-- Prove2me | Definitions.Def_MarkovProcess_Restart_RationalRestart
-- name    : MarkovProcess_Restart_RationalRestart
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T13:36:46.764977+00:00
-- url     : https://prove2.me/theorems/93091ca1-4019-4d50-b9e4-70b1b799f640
-- title:
--   MarkovProcess definitions: Restart.RationalRestart
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Restart.RationalRestart`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Restart/RationalRestart.lean#L1-L535

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
import Definitions.Def_MarkovProcess_DenseTime_PhysicalReindex
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
import Definitions.Def_MarkovProcess_DenseTime_Trajectory
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Path_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Path_DenseFiltration
import Definitions.Def_MarkovProcess_Path_Polish_SourceClosedV3
import Definitions.Def_MarkovProcess_Restart_RationalRestrictedRestart
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Definitions.Def_MarkovProcess_Trajectory_Basic
import Definitions.Def_MarkovProcess_Trajectory_FiniteMarginals
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
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
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

/-!
# The rational-time restart kernel and its joint law

This file merges the following former modules, one section each:

* `RationalJointKernel`: The rational past/future restart kernel
* `RationalRestartFiniteMarginals`: Finite marginals of the rational restart kernel
* `RationalJointLaw`: Rational-time joint restart law
-/

namespace MarkovProcess

section RationalJointKernel

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace ContinuousPath

noncomputable section

variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

/-- The complete rational-past restriction is Borel measurable. -/
theorem measurable_densePastRestriction (S : DenseTime) :
    Measurable (densePastRestriction (alpha := alpha) S) := by
  apply Measurable.of_comap_le
  rw [comap_densePastRestriction_eq_canonicalFiltration]
  exact (canonicalFiltration (alpha := alpha)).le (DenseTime.castOrderEmbedding S)



/-- The kernel which samples the rational past and then an independent future trajectory started
from the terminal state of that past. -/
def rationalPastFutureRestartKernel
    (Q : Kernel alpha (ContinuousPath alpha)) (S : DenseTime) :
    Kernel alpha ((Set.Iic S → alpha) × ContinuousPath alpha) :=
  Q.map (densePastRestriction S) ⊗ₖ
    Kernel.prodMkLeft alpha
      (Kernel.comap Q (densePastTerminal S) (measurable_densePastTerminal S))

/-- If `Q` is a Markov path kernel, then so is its rational past/future restart kernel. -/
instance instIsMarkovKernelRationalPastFutureRestartKernel
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q] (S : DenseTime) :
    IsMarkovKernel (rationalPastFutureRestartKernel Q S) := by
  unfold rationalPastFutureRestartKernel
  let : IsMarkovKernel (Q.map (densePastRestriction S)) :=
    Kernel.IsMarkovKernel.map Q (measurable_densePastRestriction S)
  infer_instance



end
end ContinuousPath

end RationalJointKernel

section RationalRestartFiniteMarginals

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open scoped NNReal


noncomputable section

namespace MixedPastFuture









variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]













end MixedPastFuture

namespace SubMarkovKernelSemigroup.IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]









end SubMarkovKernelSemigroup.IsConservative
end

end RationalRestartFiniteMarginals

section RationalJointLaw

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]



end
end IsConservative
end SubMarkovKernelSemigroup

end RationalJointLaw

end MarkovProcess


