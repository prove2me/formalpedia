-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_ParameterizedShiftCleanV1
-- name    : MarkovProcess_V3HRepair_ParameterizedShiftCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:18:01.744456+00:00
-- url     : https://prove2.me/theorems/ea302baa-c9c8-4a85-8bf0-5c129a5399a6
-- title:
--   Verified MarkovProcess source repair: ParameterizedShiftCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess ParameterizedShiftCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.ParameterizedShiftCleanV1 source SHA-256 634d2299b71067e2c6aac926c4e3c4e00bc591124b84689153154b9b6a15cc0c. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names. Additional transparent proof aliases are appended after the source declarations for original frozen theorem targets 998756d7-87e6-4a17-8fb1-9a34827cc3f6; these add no mathematical assumptions.

import Definitions.Def_MarkovProcess_V3HRepair_FellerShiftRootCleanV3
import Definitions.Def_MarkovProcess_V3HRepair_ParameterizedFiniteEvaluationCleanV1
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
open IsConservative
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
/-- Simple Markov property of the continuous-path process of a conservative Feller semigroup. -/
theorem IsFellerKernelSemigroup.continuousProcess_map_shift
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (s : NNReal) :
    (continuousProcess P hP).map (ContinuousPath.shift s) = (continuousProcess P hP).comp (P s) :=
  hFeller.continuousPathTrajectory_map_shift P hP _ hK s
end SubMarkovKernelSemigroup
namespace ParameterizedSubMarkovKernelSemigroup
variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)
/-- Freezing the parameter of the parameterized process gives the fibre's process. -/
theorem IsConservative.continuousProcess_comp_prodMk (theta : Theta) :
    (fun x ↦ IsConservative.continuousProcess P hP (theta, x)) =
      SubMarkovKernelSemigroup.IsConservative.continuousProcess
        (P.toSubMarkovKernelSemigroup theta) (hP theta) := by
  funext x
  exact IsConservative.continuousProcess_apply P hP theta x
variable [LocallyCompactSpace alpha]
  (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
include hFeller
/-- Simple Markov property of the parameterized process at deterministic time s. -/
theorem IsConservative.continuousProcess_map_shift (hK : P.KolmogorovRegular hP)
    (theta : Theta) (x : alpha) (s : NNReal) :
    (IsConservative.continuousProcess P hP (theta, x)).map (ContinuousPath.shift s) =
      ((P.toSubMarkovKernelSemigroup theta) s x).bind
        (fun y ↦ IsConservative.continuousProcess P hP (theta, y)) := by
  rw [IsConservative.continuousProcess_apply,
    ← Kernel.map_apply _ (ContinuousPath.measurable_shift_fixed s),
    (hFeller theta).continuousProcess_map_shift _ _ (hK theta) s, Kernel.comp_apply,
    IsConservative.continuousProcess_comp_prodMk]
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess

#print axioms MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_map_shift

noncomputable def MarkovProcess.V3HRepairProof_998756d787e64a178fb19a34827cc3f6 :=
  @MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_map_shift


