-- Prove2me | Definitions.Def_MarkovProcess_V3H_Main_4d46965d
-- name    : MarkovProcess_V3H_Main_4d46965d
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:16:46.33703+00:00
-- url     : https://prove2.me/theorems/db3d748b-fc4d-4401-8eb5-72cc1f0a495f
-- title:
--   MarkovProcess: MarkovProcess_V3H_Main_4d46965d
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_DenseTime_Trajectory_b0f7f66f
import Definitions.Def_MarkovProcess_V3H_DenseTime_TwoPointMarginals_b3a3d14b
import Definitions.Def_MarkovProcess_V3H_Feller_BackwardC0Integral_1512e54f
import Definitions.Def_MarkovProcess_V3H_Feller_DensePhysicalFiniteSetContinuity_75f8b26c
import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_FiniteTime_CoordinateProductActiveReduction_0fcd6a29
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelCompactTestTransport_3904fd05
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelShift_14b03019
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelRestriction_041bf9e5
import Definitions.Def_MarkovProcess_V3H_Kernel_FiniteRestrictionIdentification_619c5320
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_KolmogorovMoments_9b991370
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_Polish_87f91693
import Definitions.Def_MarkovProcess_V3H_Path_RandomShiftMeasurability_fbe17c52
import Definitions.Def_MarkovProcess_V3H_Path_ShiftCompactTestConvergence_fc2b2de1
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Definitions.Def_MarkovProcess_V3H_Path_StoppingTimeDyadicCeiling_2d75c809
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Definitions.Def_MarkovProcess_V3H_Time_FiniteDenseApproximationOrdered_4fc0c4f5
import Definitions.Def_MarkovProcess_V3H_Trajectory_AllTimeFiniteMarginals_51403fc5
import Definitions.Def_MarkovProcess_V3H_Trajectory_Basic_34bd0835
import Definitions.Def_MarkovProcess_V3H_Trajectory_DenseRestrictionMarginals_931e4c17
import Definitions.Def_MarkovProcess_V3H_Trajectory_FellerRestrictedRestart_8026f3b2
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

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

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



/-- Evaluating the continuous-path process at a nonnegative rational time gives the transition
kernel of `P` at that time. -/
theorem IsConservative.continuousProcess_map_eval
    (hK : P.KolmogorovRegular hP) (r : DenseTime) :
    (continuousProcess P hP).map (fun omega ↦ omega (DenseTime.castOrderEmbedding r)) =
      P (DenseTime.castOrderEmbedding r) :=
  _root_.MarkovProcess.SubMarkovKernelSemigroup.IsConservative.p2m_embedded_dda797d33227c489 P hP _ hK r

/-- The continuous-path process starts where it is told: its time-zero coordinate has the law of
the identity kernel, that is, the Dirac measure at the starting point. -/
theorem IsConservative.continuousProcess_map_eval_zero (hK : P.KolmogorovRegular hP) :
    (continuousProcess P hP).map (fun omega ↦ omega 0) = Kernel.id := by
  have hzero : DenseTime.castOrderEmbedding (0 : DenseTime) = (0 : NNReal) := by
    rw [DenseTime.castOrderEmbedding, NNRat.castOrderEmbedding_apply, NNRat.cast_zero]
  have heval := IsConservative.continuousProcess_map_eval P hP hK 0
  rw [hzero] at heval
  rw [heval]
  exact P.zero







variable [LocallyCompactSpace alpha]





/-- Restart at a deterministic time: after restriction to an event of the canonical filtration at
time `s`, the law of the shifted path is the process started from the time-`s` state. -/
theorem IsFellerKernelSemigroup.continuousProcess_restrict_map_shift
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (x : alpha) (s : NNReal) (A : Set (ContinuousPath alpha))
    (hA : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := alpha) s] A) :
    (((continuousProcess P hP) x).restrict A).map (ContinuousPath.shift s) =
      Kernel.comap (continuousProcess P hP)
          (ContinuousPath.coordinateProcess (alpha := alpha) s)
          (ContinuousPath.measurable_coordinateProcess s) ∘ₘ
        (((continuousProcess P hP) x).restrict A) :=
  hFeller.p2m_embedded_a6ebfc002f3abf6e P hP _ hK x s A hA



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
















omit [LocallyCompactSpace alpha] in
/-- Kolmogorov regularity follows from the intrinsic moment criterion on the semigroup. -/
theorem KolmogorovRegular.of_hasKolmogorovMoments {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) : P.KolmogorovRegular hP :=
  IsConservative.kolmogorovRegular_of_hasKolmogorovMoments P hP hmom



end


end SubMarkovKernelSemigroup

end MarkovProcess


