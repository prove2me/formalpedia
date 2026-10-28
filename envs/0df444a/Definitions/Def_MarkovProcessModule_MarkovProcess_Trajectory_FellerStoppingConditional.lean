-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Trajectory_FellerStoppingConditional
-- name    : MarkovProcessModule_MarkovProcess_Trajectory_FellerStoppingConditional
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T21:21:23.686012+00:00
-- url     : https://prove2.me/theorems/8536e4e4-7f6d-4515-bd66-a608777378c8
-- title:
--   MarkovProcess.Trajectory.FellerStoppingConditional
-- statement:
--   # Conditional expectation of the Feller trajectory at finite stopping times
--
--   For every finite `NNReal`-valued stopping time of the canonical filtration, the conditional
--   expectation of a bounded strongly measurable functional of the shifted canonical Feller
--   trajectory, given the stopped sigma-algebra, is the path-kernel expectation started from the
--   state at the stopping time.  The proof feeds the event-restricted stopping-time restart identity
--   into the generic conditional-expectation bridge; measurability of the restarted expectation for
--   the stopped sigma-algebra comes from progressive measurability of the coordinate process.
--
--   The stopping time here is finite and `NNReal`-valued.  A `WithTop`-valued time that can be
--   infinite is covered, on the event where it is finite, in `Trajectory/StoppingLtTop.lean`; no
--   Hunt-process property is asserted.
--
--   Complete pinned Lean module MarkovProcess.Trajectory.FellerStoppingConditional by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Trajectory/FellerStoppingConditional.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Trajectory_FellerStoppingRestart
import Definitions.Def_MarkovProcessModule_MarkovProcess_Path_StoppedValueMeasurability

/-!
# Conditional expectation of the Feller trajectory at finite stopping times

For every finite `NNReal`-valued stopping time of the canonical filtration, the conditional
expectation of a bounded strongly measurable functional of the shifted canonical Feller
trajectory, given the stopped sigma-algebra, is the path-kernel expectation started from the
state at the stopping time.  The proof feeds the event-restricted stopping-time restart identity
into the generic conditional-expectation bridge; measurability of the restarted expectation for
the stopped sigma-algebra comes from progressive measurability of the coordinate process.

The stopping time here is finite and `NNReal`-valued.  A `WithTop`-valued time that can be
infinite is covered, on the event where it is finite, in `Trajectory/StoppingLtTop.lean`; no
Hunt-process property is asserted.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- At a finite stopping time, the conditional expectation of a bounded functional of the shifted
Feller trajectory given the stopped sigma-algebra is its path-kernel expectation started from the
state at the stopping time. -/
theorem IsFellerKernelSemigroup.continuousPathTrajectory_condExp_shift_stoppingTime
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousPathTrajectory P hP default) x)[fun omega ↦
        F (ContinuousPath.shift (T omega) omega)|hT.measurableSpace] =ᵐ[
      (continuousPathTrajectory P hP default) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousPathTrajectory P hP default)
        (omega (T omega)) := by
  apply condExp_comp_ae_eq_integral_kernel_of_restrict_map
    ((continuousPathTrajectory P hP default) x)
    (Kernel.comap (continuousPathTrajectory P hP default) (fun omega ↦ omega (T omega))
      (ContinuousPath.measurable_eval_stoppingTime_borel T hT))
    (fun omega ↦ ContinuousPath.shift (T omega) omega)
    (ContinuousPath.measurable_shift_stoppingTime T hT)
    hT.measurableSpace_le
    (hFeller.continuousPathTrajectory_restrict_map_shift_stoppingTime P hP default hK x T hT)
    F hF ?_ C hFC
  have hBase : StronglyMeasurable[hT.measurableSpace]
      (fun omega ↦ ∫ eta, F eta ∂(continuousPathTrajectory P hP default) (omega (T omega))) :=
    hF.integral_kernel.comp_measurable (ContinuousPath.measurable_eval_stoppingTime T hT)
  simpa only [Kernel.comap_apply] using hBase

end
end MarkovProcess.SubMarkovKernelSemigroup


