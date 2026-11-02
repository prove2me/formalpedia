-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_BrownianFiniteEvaluationCleanV2
-- name    : MarkovProcess_V3HRepair_BrownianFiniteEvaluationCleanV2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T11:37:13.78019+00:00
-- url     : https://prove2.me/theorems/d5e4ce19-08d4-4eec-9eda-4ece85f990d4
-- title:
--   Verified MarkovProcess source repair: BrownianFiniteEvaluationCleanV2
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess BrownianFiniteEvaluationCleanV2 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.BrownianFiniteEvaluationCleanV2 source SHA-256 bf514c2e426a8413617ea085d1213ff6a1741c2b780d05afd6a523099136344a. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Examples_HeatSemigroup_43feba3c
import Definitions.Def_MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
import Definitions.Def_MarkovProcess_V3H_Trajectory_Dynkin_eb6ae7c0
import Definitions.Def_MarkovProcess_V3HRepair_ContinuousFiniteTimeSetIntegralClean
import Definitions.Def_MarkovProcess_V3HRepair_FellerDenseApproximationClean
import Definitions.Def_MarkovProcess_V3HRepair_ExistsDenseTimeSequence

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal ZeroAtInfty
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
namespace SubMarkovKernelSemigroup
noncomputable section
open IsConservative
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable [LocallyCompactSpace alpha]
theorem IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (I : Finset NNReal) :
    (continuousProcess P hP).map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I :=
  hFeller.continuousPathTrajectory_map_finiteTimeSet P hP _ hK I
end
end SubMarkovKernelSemigroup
end MarkovProcess

namespace MarkovProcess
noncomputable section
theorem kolmogorovRegular_heatSemigroup :
    heatSemigroup.KolmogorovRegular isConservative_heatSemigroup :=
  SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
    isConservative_heatSemigroup p2m_embedded_d699d49b7a4121f2
end
end MarkovProcess

open MarkovProcess
theorem solution (I : Finset NNReal) :
    brownianMotion.map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel heatSemigroup I :=
  isFellerKernelSemigroup_heatSemigroup.continuousProcess_map_finiteEvaluation heatSemigroup
    isConservative_heatSemigroup kolmogorovRegular_heatSemigroup I

#print axioms solution


