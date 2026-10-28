-- Prove2me | Definitions.Def_MarkovProcess_Main
-- name    : MarkovProcess_Main
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T13:41:54.141673+00:00
-- url     : https://prove2.me/theorems/c64f221f-6ee2-4e95-9634-cff63d64e5f1
-- title:
--   MarkovProcess definitions: Main
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Main`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Main.lean#L1-L405

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
import Definitions.Def_MarkovProcess_Feller_BackwardC0Recursion
import Definitions.Def_MarkovProcess_Feller_Semigroup
import Definitions.Def_MarkovProcess_FiniteTime_CoordinateProductActiveReduction
import Definitions.Def_MarkovProcess_FiniteTime_CoordinateProductNormalization
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductCoordinateNormalForm
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductStoneWeierstrass
import Definitions.Def_MarkovProcess_FiniteTime_FiniteSetKernelCompactTestTransport
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_C0_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_Integral_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KolmogorovMoments_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_PositiveC0OperatorMeasure
import Definitions.Def_MarkovProcess_Path_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Path_DenseFiltration
import Definitions.Def_MarkovProcess_Path_Polish_SourceClosedV3
import Definitions.Def_MarkovProcess_Restart_RationalRestart
import Definitions.Def_MarkovProcess_Restart_RationalRestrictedRestart
import Definitions.Def_MarkovProcess_Semigroup_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteDenseApproximationOrdered
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Definitions.Def_MarkovProcess_Trajectory_AllTimeFiniteMarginals
import Definitions.Def_MarkovProcess_Trajectory_Basic
import Definitions.Def_MarkovProcess_Trajectory_FiniteMarginals
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-!
# The continuous-path Markov process of a Feller semigroup

This is the entry point of the library: for a conservative sub-Markov kernel semigroup `P` on a
nonempty, locally compact Polish state space it names the continuous-path process
`continuousProcess P hP`, restates under quotable names the properties proved for that process
elsewhere in the library, and proves that it is the unique Markov kernel into continuous paths
with the finite-dimensional distributions of `P`.

Every statement carries the Kolmogorov regularity hypothesis `P.KolmogorovRegular hP`, which is
what gives the dense-time trajectory of `P` a continuous modification.  The shift and restart
statements carry in addition the Feller hypothesis `P.IsFellerKernelSemigroup`; the uniqueness
statements carry neither Feller continuity nor local compactness.

Nothing here asserts a Hunt-process property, and no statement covers a stopping time that can be
infinite.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

section FinsetEvaluation

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Evaluate a continuous path simultaneously at every time of a finite set of nonnegative
times, indexing the result by that set. -/
abbrev finsetEvaluation (I : Finset NNReal) : ContinuousPath alpha → (I → alpha) :=
  finiteEvaluation (fun t : I ↦ (t : NNReal))

end ContinuousPath

end FinsetEvaluation

namespace Kernel

noncomputable section DenseFiniteEvaluation

variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [MeasurableSpace beta]



section Identification

variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]



end Identification

end DenseFiniteEvaluation

end Kernel

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- Kolmogorov regularity of a conservative sub-Markov kernel semigroup: at every starting point
the canonical dense-time coordinate process of `P` satisfies a Kolmogorov--Chentsov moment bound
with an admissible Hölder exponent.

This is the hypothesis under which the dense-time trajectory of `P` admits a continuous
modification, and every statement about `continuousProcess P hP` carries it. -/
def KolmogorovRegular : Prop :=
  ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
    IsKolmogorovProcess (fun r omega ↦ omega r)
        (denseTimeTrajectory P hP DenseTime.enumeration
          DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
      0 < gamma ∧ gamma < (q - 1) / p

/-- The continuous-path process of a conservative sub-Markov kernel semigroup: the canonical
continuous trajectory kernel, with the fallback path of the underlying measurable extension fixed
once and for all.  Under `P.KolmogorovRegular hP` the choice of fallback is immaterial, by
`continuousProcess_eq_continuousPathTrajectory`. -/
def IsConservative.continuousProcess : Kernel alpha (ContinuousPath alpha) :=
  continuousPathTrajectory P hP (ContinuousMap.const NNReal (Classical.arbitrary alpha))

/-- The continuous-path process of a conservative semigroup is a Markov kernel: it assigns total
mass one to path space from every starting point. -/
instance isMarkovKernel_continuousProcess : IsMarkovKernel (continuousProcess P hP) := by
  unfold IsConservative.continuousProcess
  infer_instance













variable [LocallyCompactSpace alpha]









variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]




















end


end SubMarkovKernelSemigroup

end MarkovProcess


