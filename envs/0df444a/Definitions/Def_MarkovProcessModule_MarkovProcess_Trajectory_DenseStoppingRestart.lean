-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Trajectory_DenseStoppingRestart
-- name    : MarkovProcessModule_MarkovProcess_Trajectory_DenseStoppingRestart
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T21:11:15.314427+00:00
-- url     : https://prove2.me/theorems/0c949260-77ef-40e8-9fed-b8449b147ad6
-- title:
--   MarkovProcess.Trajectory.DenseStoppingRestart
-- statement:
--   # Conditional restart at dense-time-valued stopping times
--
--   This file specializes the countable-range stopping-time restart theorem to stopping times valued
--   in `DenseTime`.  The associated physical stopping time is obtained through
--   `DenseTime.castOrderEmbedding`; its range is countable, and deterministic restart is required and
--   proved only at physical times attained by that range.
--
--   The result is a conditional-expectation identity for the canonical continuous trajectory at
--   dense-time-valued stopping times.  An arbitrary finite `NNReal`-valued stopping time is covered
--   in `Trajectory/FellerStoppingConditional.lean`, and a stopping time that may be infinite in
--   `Trajectory/StoppingLtTop.lean`.
--
--   Complete pinned Lean module MarkovProcess.Trajectory.DenseStoppingRestart by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Trajectory/DenseStoppingRestart.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Trajectory_RationalConditional
import Definitions.Def_MarkovProcessModule_MarkovProcess_Restart_CountableStoppingRestart

/-!
# Conditional restart at dense-time-valued stopping times

This file specializes the countable-range stopping-time restart theorem to stopping times valued
in `DenseTime`.  The associated physical stopping time is obtained through
`DenseTime.castOrderEmbedding`; its range is countable, and deterministic restart is required and
proved only at physical times attained by that range.

The result is a conditional-expectation identity for the canonical continuous trajectory at
dense-time-valued stopping times.  An arbitrary finite `NNReal`-valued stopping time is covered
in `Trajectory/FellerStoppingConditional.lean`, and a stopping time that may be infinite in
`Trajectory/StoppingLtTop.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha E : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- A bounded functional of the trajectory shifted at a dense-time-valued stopping time satisfies
the path-kernel conditional-expectation formula at the corresponding physical stopping time. -/
theorem continuousPathTrajectory_condExp_shift_denseStoppingTime
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (tau : ContinuousPath alpha → DenseTime)
    (htau : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦
        ((DenseTime.castOrderEmbedding (tau omega) : NNReal) : WithTop NNReal)))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : Real) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousPathTrajectory P hP default) x)[fun omega ↦
        F (ContinuousPath.shift (DenseTime.castOrderEmbedding (tau omega)) omega)|
      htau.measurableSpace] =ᵐ[(continuousPathTrajectory P hP default) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousPathTrajectory P hP default)
        (omega (DenseTime.castOrderEmbedding (tau omega))) := by
  let tauPhysical : ContinuousPath alpha → NNReal :=
    fun omega ↦ DenseTime.castOrderEmbedding (tau omega)
  have htauRange : (Set.range tauPhysical).Countable := by
    apply (Set.countable_range
      (fun t : DenseTime ↦ DenseTime.castOrderEmbedding t)).mono
    rintro S ⟨omega, rfl⟩
    exact ⟨tau omega, rfl⟩
  apply ContinuousPath.condExp_shift_stoppingTime_ae_eq_integral_pathKernel_of_restart_on_range
    (continuousPathTrajectory P hP default) x tauPhysical htau htauRange
  · intro S hS
    obtain ⟨omega, homega⟩ := hS
    subst S
    exact continuousPathTrajectory_restrict_map_shift_denseTime
      P hP default hK x (tau omega)
  · exact hF
  · exact hFC

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


