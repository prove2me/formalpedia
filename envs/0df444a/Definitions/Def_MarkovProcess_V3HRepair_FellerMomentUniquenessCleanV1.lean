-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FellerMomentUniquenessCleanV1
-- name    : MarkovProcess_V3HRepair_FellerMomentUniquenessCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T11:37:15.362714+00:00
-- url     : https://prove2.me/theorems/f0512be5-85d3-4077-83de-f5b5e5ae0067
-- title:
--   Verified MarkovProcess source repair: FellerMomentUniquenessCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess FellerMomentUniquenessCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.FellerMomentUniquenessCleanV1 source SHA-256 6552487ef23170c8fe69d1ce509c2b0e419a49afd30baf166c8f1eb217164c2a. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_DenseTime_TwoPointMarginals_b3a3d14b
import Definitions.Def_MarkovProcess_V3H_Feller_BackwardC0Integral_1512e54f
import Definitions.Def_MarkovProcess_V3H_Feller_DensePhysicalFiniteSetContinuity_75f8b26c
import Definitions.Def_MarkovProcess_V3H_FiniteTime_CoordinateProductActiveReduction_0fcd6a29
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelCompactTestTransport_3904fd05
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelShift_14b03019
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelRestriction_041bf9e5
import Definitions.Def_MarkovProcess_V3H_Kernel_FiniteRestrictionIdentification_619c5320
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_Polish_87f91693
import Definitions.Def_MarkovProcess_V3H_Path_RandomShiftMeasurability_fbe17c52
import Definitions.Def_MarkovProcess_V3H_Path_ShiftCompactTestConvergence_fc2b2de1
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Definitions.Def_MarkovProcess_V3H_Path_StoppingTimeDyadicCeiling_2d75c809
import Definitions.Def_MarkovProcess_V3H_Time_FiniteDenseApproximationOrdered_4fc0c4f5
import Definitions.Def_MarkovProcess_V3H_Trajectory_DenseRestrictionMarginals_931e4c17
import Definitions.Def_MarkovProcess_V3H_Trajectory_FellerRestrictedRestart_8026f3b2
import Definitions.Def_MarkovProcess_V3HRepair_KernelFiniteRestrictionIdentificationCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_KernelDenseRestrictionInjectiveCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_KernelDenseRestriction
import Definitions.Def_MarkovProcess_V3HRepair_ContinuousFiniteDenseTimeSet
import Definitions.Def_MarkovProcess_V3HRepair_ContinuousFiniteTimeSetIntegralClean
import Definitions.Def_MarkovProcess_V3HRepair_FellerDenseApproximationClean
import Definitions.Def_MarkovProcess_V3HRepair_ExistsDenseTimeSequence

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal
namespace MarkovProcess
namespace Kernel
noncomputable section
variable {alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]
variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]
theorem map_denseRestriction_eq_iff {kappa eta : Kernel beta (ContinuousPath alpha)} :
    kappa.map ContinuousPath.denseRestriction = eta.map ContinuousPath.denseRestriction ↔
      kappa = eta := by
  constructor
  · intro h
    exact map_denseRestriction_injective (alpha := alpha) (beta := beta) h
  · exact fun h ↦ congrArg
      (fun z : Kernel beta (ContinuousPath alpha) ↦
        z.map ContinuousPath.denseRestriction) h
end
end Kernel
end MarkovProcess

namespace MarkovProcess
noncomputable section
theorem exists_denseTime_finset_seq_tendsto (I : Finset NNReal) :
    ∃ q : ℕ → I ↪o DenseTime,
      ∀ t, Tendsto (fun k ↦ DenseTime.castOrderEmbedding (q k t))
        atTop (nhds (t : NNReal)) := by
  simpa only using! exists_denseTime_finiteOrderEmbedding_seq_tendsto
    (OrderEmbedding.subtype (fun t : NNReal ↦ t ∈ I))
end
end MarkovProcess

namespace MarkovProcess
noncomputable section
variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [LocallyCompactSpace alpha]
namespace SubMarkovKernelSemigroup
open IsConservative
variable [CompleteSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]
theorem IsFellerKernelSemigroup.continuousPathTrajectory_map_finiteTimeSet
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (I : Finset NNReal) :
    (continuousPathTrajectory P hP default).map
        (ContinuousPath.finiteEvaluation (fun t : I ↦ (t : NNReal))) =
      finiteSetKernel P I := by
  obtain ⟨q, hq⟩ := exists_denseTime_finset_seq_tendsto I
  apply IsConservative.continuousPathTrajectory_map_finiteTimeSet_of_integral_tendsto
    P hP default hK I q hq
  intro x f
  exact hFeller.tendsto_integral_compactlySupported_finiteDenseApproximationKernel
    hP q hq f x
end SubMarkovKernelSemigroup
end
end MarkovProcess

namespace MarkovProcess
namespace Kernel
noncomputable section
variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [MeasurableSpace beta]
variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]
theorem eq_of_map_denseFiniteEvaluation_eq
    (kappa eta : Kernel beta (ContinuousPath alpha)) [IsFiniteKernel kappa]
    (h : ∀ I : Finset DenseTime,
      kappa.map (ContinuousPath.finsetEvaluation
          (SubMarkovKernelSemigroup.denseTimePhysicalSet I)) =
        eta.map (ContinuousPath.finsetEvaluation
          (SubMarkovKernelSemigroup.denseTimePhysicalSet I))) :
    kappa = eta := by
  rw [← map_denseRestriction_eq_iff (alpha := alpha) (beta := beta)]
  apply eq_of_map_finiteRestriction_eq
  intro I
  rw [map_denseRestriction_map_restrict kappa I, map_denseRestriction_map_restrict eta I, h I]
end
end Kernel
end MarkovProcess

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
noncomputable section
open IsConservative
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
theorem IsConservative.continuousProcess_map_finiteEvaluation_denseTime
    (hK : P.KolmogorovRegular hP) (I : Finset DenseTime) :
    (continuousProcess P hP).map
        (ContinuousPath.finsetEvaluation (denseTimePhysicalSet I)) =
      finiteSetKernel P (denseTimePhysicalSet I) :=
  continuousPathTrajectory_map_finiteDenseTimeSet P hP _ hK I
variable [LocallyCompactSpace alpha]
theorem IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (I : Finset NNReal) :
    (continuousProcess P hP).map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I :=
  hFeller.continuousPathTrajectory_map_finiteTimeSet P hP _ hK I
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
omit [LocallyCompactSpace alpha] in
/-- Uniqueness from rational times: a finite kernel into continuous paths whose evaluations at
the finite sets of physical times carried by rational labels are the finite-set kernels of `P` is
the continuous-path process of `P`.  Neither Feller continuity nor local compactness is used. -/
theorem IsConservative.eq_continuousProcess_of_map_finiteEvaluation_denseTime
    (hK : P.KolmogorovRegular hP) (Q : Kernel alpha (ContinuousPath alpha)) [IsFiniteKernel Q]
    (hQ : ∀ I : Finset DenseTime,
      Q.map (ContinuousPath.finsetEvaluation (denseTimePhysicalSet I)) =
        finiteSetKernel P (denseTimePhysicalSet I)) :
    Q = continuousProcess P hP :=
  Kernel.eq_of_map_denseFiniteEvaluation_eq Q _ fun I ↦
    (hQ I).trans (continuousProcess_map_finiteEvaluation_denseTime P hP hK I).symm
omit [LocallyCompactSpace alpha] in
/-- Uniqueness: a finite kernel into continuous paths with the finite-dimensional distributions of
`P` is the continuous-path process of `P`.  Only rational times are read off the hypothesis, so
neither Feller continuity nor local compactness is used. -/
theorem IsConservative.eq_continuousProcess_of_map_finiteEvaluation
    (hK : P.KolmogorovRegular hP) (Q : Kernel alpha (ContinuousPath alpha)) [IsFiniteKernel Q]
    (hQ : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I) :
    Q = continuousProcess P hP :=
  IsConservative.eq_continuousProcess_of_map_finiteEvaluation_denseTime P hP hK Q fun I ↦
    hQ (denseTimePhysicalSet I)
theorem IsFellerKernelSemigroup.existsUnique_continuousProcess
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) :
    ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I := by
  refine ⟨continuousProcess P hP,
    ⟨inferInstance, hFeller.continuousProcess_map_finiteEvaluation P hP hK⟩, ?_⟩
  rintro Q ⟨hQ, hmarg⟩
  let : IsMarkovKernel Q := hQ
  exact IsConservative.eq_continuousProcess_of_map_finiteEvaluation P hP hK Q hmarg
end
end SubMarkovKernelSemigroup
end MarkovProcess

open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open MeasureTheory ProbabilityTheory
open scoped NNReal
open IsConservative
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
include hP in

theorem solution
    (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) :
    ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I :=
  hFeller.existsUnique_continuousProcess P hP (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom)

#print axioms solution


