-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FellerShiftRootCleanV3
-- name    : MarkovProcess_V3HRepair_FellerShiftRootCleanV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:14:53.269916+00:00
-- url     : https://prove2.me/theorems/5f8cd260-a899-438f-87a5-a513a1bea8f1
-- title:
--   Verified MarkovProcess source repair: FellerShiftRootCleanV3
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess FellerShiftRootCleanV3 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.FellerShiftRootCleanV3 source SHA-256 804f929026054164318ef56074f6e955de30d0f878c37f7d5ef8a0e26f17daca. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names. Additional transparent proof aliases are appended after the source declarations for original frozen theorem targets 22081c63-f373-4a0f-867c-8a3df3bb6e51; these add no mathematical assumptions.

import Definitions.Def_MarkovProcess_V3HRepair_FiniteSetKernelTranslationCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_TranslateMeasurabilityCleanV1
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_V3HRepair_KernelDenseRestrictionInjectiveCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_DenseRestrictionMarginalsCleanV3
import Definitions.Def_MarkovProcess_V3HRepair_FellerMomentUniquenessCleanV1
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelShift_14b03019
import Definitions.Def_MarkovProcess_V3HRepair_KernelFiniteRestrictionIdentificationCleanV1

/-!
# Deterministic shifts of Feller trajectory laws

The canonical continuous trajectory of a conservative Feller kernel semigroup restarts after
every deterministic nonnegative time. The proof identifies all finite coordinates of the dense
restriction and then uses injectivity of dense restriction on continuous-path kernels.

This is an unconditional kernel-law identity. The conditional form is in
`Trajectory/FellerConditional.lean` and the strong Markov property in
`Trajectory/FellerStoppingRestart.lean`; no Hunt-process property is asserted.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

/-- Shifting the canonical continuous trajectory by a deterministic nonnegative time gives the
trajectory law mixed against the transition kernel at that time. -/
theorem IsFellerKernelSemigroup.continuousPathTrajectory_map_shift
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (s : NNReal) :
    (continuousPathTrajectory P hP default).map (ContinuousPath.shift s) =
      (continuousPathTrajectory P hP default).comp (P s) := by
  let Q := continuousPathTrajectory P hP default
  apply Kernel.map_denseRestriction_injective
  apply Kernel.eq_of_map_finiteRestriction_eq
  intro I
  let S := denseTimePhysicalSet I
  let U := finiteSetTranslate s S
  have hShift := ContinuousPath.measurable_shift_fixed (alpha := alpha) s
  have hDense := ContinuousPath.measurable_denseRestriction (alpha := alpha)
  have hRestrict := Finset.measurable_restrict (X := fun _ ↦ alpha) I
  have hEval : Measurable
      (ContinuousPath.finiteEvaluation (α := alpha) (fun t : U ↦ (t : NNReal))) :=
    (ContinuousPath.continuous_finiteEvaluation
      (α := alpha) (fun t : U ↦ (t : NNReal))).measurable
  have hTranslate := measurable_pullbackFiniteSetTranslate (alpha := alpha) s S
  have hPhysical := DenseTimePath.measurable_pullbackPhysicalSet (alpha := alpha) I
  have hcoordinates :
      I.restrict ∘ (ContinuousPath.denseRestriction (alpha := alpha) ∘
          ContinuousPath.shift (alpha := alpha) s) =
        (DenseTimePath.pullbackPhysicalSet (alpha := alpha) I ∘
          pullbackFiniteSetTranslate (alpha := alpha) s S) ∘
            ContinuousPath.finiteEvaluation (α := alpha)
              (fun t : U ↦ (t : NNReal)) := by
    funext omega t
    change omega (s + DenseTime.castOrderEmbedding t) =
      omega ((finiteSetTranslateEquiv s S
        (DenseTime.physicalSetEquiv I t) : U) : NNReal)
    rw [finiteSetTranslateEquiv_apply]
    rw [DenseTime.physicalSetEquiv_apply]
  calc
    (((Q.map (ContinuousPath.shift s)).map ContinuousPath.denseRestriction).map
          I.restrict) =
        Q.map (I.restrict ∘
          (ContinuousPath.denseRestriction ∘ ContinuousPath.shift s)) := by
      rw [← Kernel.map_comp_right (Q.map (ContinuousPath.shift s)) hDense hRestrict,
        ← Kernel.map_comp_right Q hShift (hRestrict.comp hDense)]
      rw [Function.comp_assoc]
    _ = Q.map ((DenseTimePath.pullbackPhysicalSet I ∘
          pullbackFiniteSetTranslate s S) ∘
            ContinuousPath.finiteEvaluation (fun t : U ↦ (t : NNReal))) := by
      rw [hcoordinates]
    _ = ((Q.map (ContinuousPath.finiteEvaluation
          (fun t : U ↦ (t : NNReal)))).map
            (pullbackFiniteSetTranslate s S)).map
              (DenseTimePath.pullbackPhysicalSet I) := by
      rw [Kernel.map_comp_right Q hEval (hPhysical.comp hTranslate),
        Kernel.map_comp_right (Q.map
          (ContinuousPath.finiteEvaluation (fun t : U ↦ (t : NNReal))))
          hTranslate hPhysical]
    _ = ((finiteSetKernel P U).map (pullbackFiniteSetTranslate s S)).map
          (DenseTimePath.pullbackPhysicalSet I) := by
      rw [hFeller.continuousPathTrajectory_map_finiteTimeSet P hP default hK U]
    _ = ((finiteSetKernel P S).comp (P s)).map
          (DenseTimePath.pullbackPhysicalSet I) := by
      rw [hP.finiteSetKernel_map_pullback_translate P s S]
    _ = ((finiteSetKernel P S).map
          (DenseTimePath.pullbackPhysicalSet I)).comp (P s) := by
      rw [Kernel.map_comp]
    _ = (((Q.map ContinuousPath.denseRestriction).map I.restrict).comp (P s)) := by
      rw [IsConservative.continuousPathTrajectory_map_denseRestriction_map_restrict
        P hP default hK I]
    _ = (((Q.comp (P s)).map ContinuousPath.denseRestriction).map I.restrict) := by
      rw [Kernel.map_comp, Kernel.map_comp]

end
end SubMarkovKernelSemigroup
end MarkovProcess

#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousPathTrajectory_map_shift

noncomputable def MarkovProcess.V3HRepairProof_22081c63f3734a0f867c8a3df3bb6e51 :=
  @MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousPathTrajectory_map_shift


