-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_ParameterizedFiniteEvaluationCleanV1
-- name    : MarkovProcess_V3HRepair_ParameterizedFiniteEvaluationCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:14:47.315206+00:00
-- url     : https://prove2.me/theorems/a2783b15-fd83-408e-af52-d45d1ba42f45
-- title:
--   Verified MarkovProcess source repair: ParameterizedFiniteEvaluationCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess ParameterizedFiniteEvaluationCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.ParameterizedFiniteEvaluationCleanV1 source SHA-256 be06bf9df5aff1616ac33e5e66eaa047a76374201a0a481efbe42046e676cae9. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Definitions.Def_MarkovProcess_V3HRepair_FellerMomentUniquenessCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_FinsetEvaluationMeasurabilityCleanV1
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup
variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)
/-- Finite-dimensional distributions at rational times, without any Feller hypothesis. -/
theorem IsConservative.continuousProcess_map_finiteEvaluation_denseTime
    (hK : P.KolmogorovRegular hP) (theta : Theta) (x : alpha) (I : Finset DenseTime) :
    (IsConservative.continuousProcess P hP (theta, x)).map
        (ContinuousPath.finsetEvaluation (SubMarkovKernelSemigroup.denseTimePhysicalSet I)) =
      SubMarkovKernelSemigroup.finiteSetKernel (P.toSubMarkovKernelSemigroup theta)
        (SubMarkovKernelSemigroup.denseTimePhysicalSet I) x := by
  rw [IsConservative.continuousProcess_apply,
    ← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _),
    SubMarkovKernelSemigroup.IsConservative.continuousProcess_map_finiteEvaluation_denseTime _ _
      (hK theta)]

variable [LocallyCompactSpace alpha]
  (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)

include hFeller

/-- Finite-dimensional distributions at all real times: under the parameterized process at
`(theta, x)`, the law of the coordinates at a finite set `I` of times is the finite-set kernel of
the semigroup at `theta`, started at `x`. -/
theorem IsConservative.continuousProcess_map_finiteEvaluation (hK : P.KolmogorovRegular hP)
    (theta : Theta) (x : alpha) (I : Finset NNReal) :
    (IsConservative.continuousProcess P hP (theta, x)).map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel (P.toSubMarkovKernelSemigroup theta) I x := by
  rw [IsConservative.continuousProcess_apply,
    ← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _),
    (hFeller theta).continuousProcess_map_finiteEvaluation _ _ (hK theta)]


end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess

#print axioms MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_map_finiteEvaluation


