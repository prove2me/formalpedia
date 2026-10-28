-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Feller_DensePhysicalFiniteSetContinuity
-- name    : MarkovProcessModule_MarkovProcess_Feller_DensePhysicalFiniteSetContinuity
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T20:56:30.800333+00:00
-- url     : https://prove2.me/theorems/1c7e0ac9-039b-4293-adc4-7acb0f9aabaf
-- title:
--   MarkovProcess.Feller.DensePhysicalFiniteSetContinuity
-- statement:
--   # Compact-test bounds for finite dense-time laws
--
--   Compact-test integrals against a physically indexed finite-set kernel, reindexed by dense-time
--   labels, are continuous in the starting point. Conservativity also gives a uniform norm bound by
--   the `C₀` norm of the test. Both statements include the empty coordinate set.
--
--   This is finite-dimensional analytic infrastructure; no statement about path space is proved
--   here.  The continuous-path process is built in `Trajectory/`.
--
--   Complete pinned Lean module MarkovProcess.Feller.DensePhysicalFiniteSetContinuity by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Feller/DensePhysicalFiniteSetContinuity.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_DenseTime_PhysicalCompactTestTransport
import Definitions.Def_MarkovProcessModule_MarkovProcess_Feller_FiniteSetCompactTestContinuity
import Definitions.Def_MarkovProcessModule_MarkovProcess_Kernel_PositiveC0OperatorMeasure

/-!
# Compact-test bounds for finite dense-time laws

Compact-test integrals against a physically indexed finite-set kernel, reindexed by dense-time
labels, are continuous in the starting point. Conservativity also gives a uniform norm bound by
the `C₀` norm of the test. Both statements include the empty coordinate set.

This is finite-dimensional analytic infrastructure; no statement about path space is proved
here.  The continuous-path process is built in `Trajectory/`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

section Continuity

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

/-- A compact-test integral against a finite dense-time law is continuous in the starting
point. -/
theorem IsFellerKernelSemigroup.continuous_integral_map_finiteSetKernel_pullbackPhysicalSet
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    Continuous fun y ↦ ∫ z, f z ∂
      (finiteSetKernel P (denseTimePhysicalSet J)).map
        (DenseTimePath.pullbackPhysicalSet J) y := by
  have h := hFeller.continuous_integral_compactlySupported_finiteSetKernel hP
    (denseTimePhysicalSet J) (DenseTimePath.pullbackPhysicalSetCompactTest J f)
  simpa only [DenseTimePath.integral_map_finiteSetKernel_pullbackPhysicalSet P J f] using h

end Continuity

section Bound

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]

/-- A compact-test integral against a conservative finite dense-time law is bounded by the
test's canonical `C₀` norm. -/
theorem IsConservative.norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsConservative)
    (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) (y : alpha) :
    ‖∫ z, f z ∂(finiteSetKernel P (denseTimePhysicalSet J)).map
        (DenseTimePath.pullbackPhysicalSet J) y‖ ≤
      ‖PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f‖ := by
  let K := (finiteSetKernel P (denseTimePhysicalSet J)).map
    (DenseTimePath.pullbackPhysicalSet J)
  let : IsMarkovKernel K := by
    let : IsMarkovKernel (finiteSetKernel P (denseTimePhysicalSet J)) :=
      hP.isMarkovKernel_finiteSetKernel P (denseTimePhysicalSet J)
    exact Kernel.IsMarkovKernel.map _ (DenseTimePath.measurable_pullbackPhysicalSet J)
  let : IsProbabilityMeasure (K y) := IsMarkovKernel.isProbabilityMeasure y
  let f₀ : C₀(J → alpha, ℝ) :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  change ‖∫ z, f z ∂K y‖ ≤ ‖f₀‖
  calc
    ‖∫ z, f z ∂K y‖ ≤ ‖f₀‖ * (K y).real Set.univ :=
      MeasureTheory.norm_integral_le_of_norm_le_const
        (ae_of_all _ fun z ↦ by
          simpa only [f₀,
            PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply] using!
            f₀.toBCF.norm_coe_le_norm z)
    _ = ‖f₀‖ := by
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]

end Bound

end MarkovProcess.SubMarkovKernelSemigroup


