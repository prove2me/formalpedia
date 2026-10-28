-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Restart_RationalRestrictedRestart
-- name    : MarkovProcessModule_MarkovProcess_Restart_RationalRestrictedRestart
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:47:15.2665+00:00
-- url     : https://prove2.me/theorems/7ce2eecb-46cf-42f1-9632-9e19f68b0715
-- title:
--   MarkovProcess.Restart.RationalRestrictedRestart
-- statement:
--   # Restricted restart at rational times
--
--   This file turns a full joint-law factorization of the rational past and shifted future into the
--   event-restricted restart identity on the canonical continuous-path filtration.  The joint-law
--   factorization remains an explicit input; proving it from the finite-dimensional Markov laws is the
--   next process-construction step.
--
--   Complete pinned Lean module MarkovProcess.Restart.RationalRestrictedRestart by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Restart/RationalRestrictedRestart.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Path_DenseFiltration
import Definitions.Def_MarkovProcessModule_MarkovProcess_Path_Shift
import Definitions.Def_MarkovProcessModule_MarkovProcess_Restart_RestrictedRestartOfJoint

/-!
# Restricted restart at rational times

This file turns a full joint-law factorization of the rational past and shifted future into the
event-restricted restart identity on the canonical continuous-path filtration.  The joint-law
factorization remains an explicit input; proving it from the finite-dimensional Markov laws is the
next process-construction step.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ContinuousPath

noncomputable section

variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

/-- Evaluation of a rational past at its terminal coordinate. -/
def densePastTerminal (S : DenseTime) (history : Set.Iic S → alpha) : alpha :=
  history ⟨S, Set.mem_Iic.mpr le_rfl⟩

omit [MetricSpace alpha] [BorelSpace alpha] in
/-- Terminal-coordinate evaluation on rational pasts is measurable. -/
theorem measurable_densePastTerminal (S : DenseTime) :
    Measurable (densePastTerminal (alpha := alpha) S) :=
  measurable_pi_apply (⟨S, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic S)

omit [MeasurableSpace alpha] [BorelSpace alpha] in
/-- The terminal coordinate of the rational-past restriction is the physical-time coordinate at
the rational terminal time. -/
@[simp]
theorem densePastTerminal_densePastRestriction (S : DenseTime) (omega : ContinuousPath alpha) :
    densePastTerminal S (densePastRestriction S omega) =
      coordinateProcess (alpha := alpha) (DenseTime.castOrderEmbedding S) omega :=
  rfl

/-- A joint factorization of rational past and shifted future yields the restart identity after
restriction to every event in the canonical filtration at the rational terminal time. -/
theorem restrict_map_shift_eq_pathKernel_comp_of_rational_joint
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (x : alpha) (S : DenseTime)
    (hJoint :
      (Q x).map (fun omega ↦
          (densePastRestriction S omega,
            shift (DenseTime.castOrderEmbedding S) omega)) =
        ((Q x).map (densePastRestriction S)) ⊗ₘ
          Kernel.comap Q (densePastTerminal S) (measurable_densePastTerminal S)) :
    ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[canonicalFiltration (alpha := alpha)
        (DenseTime.castOrderEmbedding S)] A →
        ((Q x).restrict A).map (shift (DenseTime.castOrderEmbedding S)) =
          Kernel.comap Q
              (coordinateProcess (alpha := alpha) (DenseTime.castOrderEmbedding S))
              (measurable_coordinateProcess (DenseTime.castOrderEmbedding S)) ∘ₘ
            ((Q x).restrict A) := by
  have hPast : Measurable (densePastRestriction (alpha := alpha) S) := by
    apply Measurable.of_comap_le
    rw [comap_densePastRestriction_eq_canonicalFiltration]
    exact (canonicalFiltration (alpha := alpha)).le (DenseTime.castOrderEmbedding S)
  have hRestricted := restrict_map_eq_comap_comp_of_map_prodMk_eq_compProd
    (Q x) (densePastRestriction S) hPast
    (shift (DenseTime.castOrderEmbedding S))
    (measurable_shift_fixed (DenseTime.castOrderEmbedding S))
    (Kernel.comap Q (densePastTerminal S) (measurable_densePastTerminal S)) hJoint
  intro A hA
  have hA' : MeasurableSet[
      MeasurableSpace.comap (densePastRestriction (alpha := alpha) S) inferInstance] A := by
    rw [comap_densePastRestriction_eq_canonicalFiltration]
    exact hA
  have hKernel :
      (Kernel.comap Q (densePastTerminal S) (measurable_densePastTerminal S)).comap
          (densePastRestriction S) hPast =
        Kernel.comap Q
          (coordinateProcess (alpha := alpha) (DenseTime.castOrderEmbedding S))
          (measurable_coordinateProcess (DenseTime.castOrderEmbedding S)) := by
    rw [← Kernel.comap_comp_right Q hPast (measurable_densePastTerminal S)]
    congr 1
  rw [← hKernel]
  exact hRestricted A hA'

end
end ContinuousPath
end MarkovProcess


