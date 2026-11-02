-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_AnnealedFiniteEvaluationCleanV1
-- name    : MarkovProcess_V3HRepair_AnnealedFiniteEvaluationCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:17:31.66603+00:00
-- url     : https://prove2.me/theorems/4b741698-9869-4727-b31a-271f75f2b8a5
-- title:
--   Verified MarkovProcess source repair: AnnealedFiniteEvaluationCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess AnnealedFiniteEvaluationCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.AnnealedFiniteEvaluationCleanV1 source SHA-256 5f0a0aa41214d825a75339e3e22ba79b063f35490b248cdac64ae9901634b12e. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names. Additional transparent proof aliases are appended after the source declarations for original frozen theorem targets 95983780-6f26-49ba-9f8b-4e9b5d0cd764; these add no mathematical assumptions.

import Definitions.Def_MarkovProcess_V3HRepair_ParameterizedFiniteEvaluationCleanV1
import Definitions.Def_MarkovProcess_V3H_Parameterized_Annealed_005d5fdd
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup
variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)
variable (mu : Measure Theta) [SFinite mu]
omit [SFinite mu] in
/-- Freezing the starting state, the quenched law is a measurable function of the parameter. -/
theorem IsConservative.measurable_continuousProcess_prodMk (x : alpha) :
    Measurable fun theta ↦ IsConservative.continuousProcess P hP (theta, x) :=
  (IsConservative.continuousProcess P hP).measurable.comp (measurable_id.prodMk measurable_const)

/-- The annealed law at a starting point is the `mu`-average of the quenched laws. -/
theorem IsConservative.annealedProcess_apply (x : alpha) :
    IsConservative.annealedProcess P hP mu x =
      mu.bind (fun theta ↦ IsConservative.continuousProcess P hP (theta, x)) := by
  rw [IsConservative.annealedProcess, Kernel.comp_apply, Kernel.prod_apply, Kernel.const_apply,
    Kernel.id_apply, Measure.prod_dirac]
  have hpm : Measurable fun theta : Theta ↦ (theta, x) := measurable_prodMk_right
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (IsConservative.measurable_continuousProcess_prodMk P hP x).aemeasurable,
    lintegral_map ((IsConservative.continuousProcess P hP).measurable_coe hs) hpm]


variable [LocallyCompactSpace alpha]
/-- The annealed finite-dimensional distributions are the `mu`-averages of the quenched ones:
on every measurable set `s` of the coordinate space, the annealed law of the coordinates at `I`
is the average over the parameter of the finite-set kernels of the semigroups. -/
theorem IsConservative.annealedProcess_map_finiteEvaluation_apply
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (x : alpha) (I : Finset NNReal) {s : Set (I → alpha)}
    (hs : MeasurableSet s) :
    (IsConservative.annealedProcess P hP mu x).map (ContinuousPath.finsetEvaluation I) s =
      ∫⁻ theta, SubMarkovKernelSemigroup.finiteSetKernel (P.toSubMarkovKernelSemigroup theta) I x s
        ∂mu := by
  have hphi : Measurable (ContinuousPath.finsetEvaluation (alpha := alpha) I) :=
    ContinuousPath.measurable_finsetEvaluation I
  rw [Measure.map_apply hphi hs, IsConservative.annealedProcess_apply,
    Measure.bind_apply (hphi hs) (IsConservative.measurable_continuousProcess_prodMk P hP x).aemeasurable]
  refine lintegral_congr fun theta ↦ ?_
  rw [← Measure.map_apply hphi hs,
    IsConservative.continuousProcess_map_finiteEvaluation P hP hFeller hK theta x I]


end MarkovProcess.ParameterizedSubMarkovKernelSemigroup

#print axioms MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.annealedProcess_map_finiteEvaluation_apply

noncomputable def MarkovProcess.V3HRepairProof_959837806f2649ba9f8b4e9b5d0cd764 :=
  @MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.annealedProcess_map_finiteEvaluation_apply


