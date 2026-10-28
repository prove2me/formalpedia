-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Trajectory_DenseRestrictionIntegral
-- name    : MarkovProcessModule_MarkovProcess_Trajectory_DenseRestrictionIntegral
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T21:01:02.7396+00:00
-- url     : https://prove2.me/theorems/f0d95d77-e183-48d2-85d3-ac2570119055
-- title:
--   MarkovProcess.Trajectory.DenseRestrictionIntegral
-- statement:
--   # Finite dense-time marginals of a restarted trajectory law
--
--   Composing the canonical continuous trajectory kernel with a measurable evaluation of the path
--   and pushing to a finite set of dense times integrates a compactly supported test through the
--   mapped finite-set kernel at the evaluated state.  The evaluation is arbitrary, so the identity
--   serves deterministic coordinates and stopping-time evaluations alike.
--
--   This is a kernel-level identity of finite-dimensional integrals.  No conditional or
--   stopping-time statement is proved here; those are in `Trajectory/FellerConditional.lean` and
--   `Trajectory/FellerStoppingConditional.lean`.
--
--   Complete pinned Lean module MarkovProcess.Trajectory.DenseRestrictionIntegral by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Trajectory/DenseRestrictionIntegral.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Trajectory_DenseRestrictionMarginals
import Definitions.Def_MarkovProcessModule_MarkovProcess_Feller_DensePhysicalFiniteSetContinuity
import Definitions.Def_MarkovProcessModule_MarkovProcess_Path_Polish

/-!
# Finite dense-time marginals of a restarted trajectory law

Composing the canonical continuous trajectory kernel with a measurable evaluation of the path
and pushing to a finite set of dense times integrates a compactly supported test through the
mapped finite-set kernel at the evaluated state.  The evaluation is arbitrary, so the identity
serves deterministic coordinates and stopping-time evaluations alike.

This is a kernel-level identity of finite-dimensional integrals.  No conditional or
stopping-time statement is proved here; those are in `Trajectory/FellerConditional.lean` and
`Trajectory/FellerStoppingConditional.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

/-- Pushing the trajectory kernel restarted at a measurable evaluation to finitely many dense
times integrates a compact test through the mapped finite-set kernel at the evaluated state. -/
theorem continuousPathTrajectory_integral_map_denseRestriction_map_restrict_comp_comap
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (mu : Measure (ContinuousPath alpha)) [IsFiniteMeasure mu]
    (e : ContinuousPath alpha → alpha) (he : Measurable e)
    (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    ∫ z, f z ∂(((Kernel.comap (continuousPathTrajectory P hP default) e he ∘ₘ mu).map
        ContinuousPath.denseRestriction).map J.restrict) =
      ∫ omega, (∫ z, f z ∂((finiteSetKernel P (denseTimePhysicalSet J)).map
        (DenseTimePath.pullbackPhysicalSet J)) (e omega)) ∂mu := by
  let Q := continuousPathTrajectory P hP default
  let KJ := (finiteSetKernel P (denseTimePhysicalSet J)).map
    (DenseTimePath.pullbackPhysicalSet J)
  have hdense := ContinuousPath.measurable_denseRestriction (alpha := alpha)
  have hrestrict := Finset.measurable_restrict (X := fun _ ↦ alpha) J
  have hQJ : (Q.map ContinuousPath.denseRestriction).map J.restrict = KJ :=
    continuousPathTrajectory_map_denseRestriction_map_restrict P hP default hK J
  have hkernel :
      ((Kernel.comap Q e he).map ContinuousPath.denseRestriction).map J.restrict =
        Kernel.comap KJ e he := by
    rw [← Kernel.comap_map_comm Q he hdense,
      ← Kernel.comap_map_comm (Q.map ContinuousPath.denseRestriction) he hrestrict, hQJ]
  have hmeasure :
      (((Kernel.comap Q e he ∘ₘ mu).map ContinuousPath.denseRestriction).map J.restrict) =
        Kernel.comap KJ e he ∘ₘ mu := by
    rw [Measure.map_comp mu _ hdense, Measure.map_comp mu _ hrestrict, hkernel]
  rw [hmeasure, Measure.comp_eq_comp_const_apply]
  let : IsMarkovKernel KJ := by
    dsimp only [KJ]
    let : IsMarkovKernel (finiteSetKernel P (denseTimePhysicalSet J)) :=
      hP.isMarkovKernel_finiteSetKernel P (denseTimePhysicalSet J)
    exact Kernel.IsMarkovKernel.map _ (DenseTimePath.measurable_pullbackPhysicalSet J)
  let : IsMarkovKernel (Kernel.comap KJ e he) := inferInstance
  let : IsFiniteMeasure ((Kernel.comap KJ e he ∘ₘ mu)) := inferInstance
  have hfint : Integrable f (Kernel.comap KJ e he ∘ₘ mu) := f.integrable
  rw [Measure.comp_eq_comp_const_apply] at hfint
  have hi := Kernel.integral_comp hfint
  simpa only [Kernel.const_apply, Kernel.comap_apply, Q, KJ] using hi

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


