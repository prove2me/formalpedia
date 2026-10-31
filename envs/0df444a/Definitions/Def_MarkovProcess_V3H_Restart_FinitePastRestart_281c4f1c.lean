-- Prove2me | Definitions.Def_MarkovProcess_V3H_Restart_FinitePastRestart_281c4f1c
-- name    : MarkovProcess_V3H_Restart_FinitePastRestart_281c4f1c
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:32:25.450203+00:00
-- url     : https://prove2.me/theorems/4d0ab699-b59a-4220-99b0-1059e1fecf82
-- title:
--   MarkovProcess: MarkovProcess_V3H_Restart_FinitePastRestart_281c4f1c
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Kernel_FiniteRestrictionIdentification_619c5320
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying joint laws of a finite past and a continuous future

A kernel whose values consist of a finite-coordinate past and a continuous future path is
determined by all finite coordinate marginals which retain coordinates from both pieces.  This is
the uniqueness step needed to upgrade finite-dimensional restart identities to a whole-future
joint-law factorization.  It does not assert that any particular stochastic process has those
finite-dimensional identities.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace Kernel

noncomputable section

variable {index alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

/-- Encode a finite-coordinate past and the dense restriction of a continuous future as one path
indexed by the disjoint union of the past and future coordinate types. -/
def finitePastDenseFuture
    (z : (index → alpha) × ContinuousPath alpha) : index ⊕ DenseTime → alpha
  | Sum.inl i => z.1 i
  | Sum.inr t => ContinuousPath.denseRestriction z.2 t

omit [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)] in
theorem measurable_finitePastDenseFuture :
    Measurable (finitePastDenseFuture (index := index) (alpha := alpha)) := by
  rw [measurable_pi_iff]
  rintro (i | t)
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply t).comp
      (ContinuousPath.measurable_denseRestriction.comp measurable_snd)

private def finitePastContinuousFuture
    (default : ContinuousPath alpha) (z : index ⊕ DenseTime → alpha) :
    (index → alpha) × ContinuousPath alpha :=
  (fun i ↦ z (Sum.inl i),
    ContinuousPath.continuousExtension default (fun t ↦ z (Sum.inr t)))

private theorem measurable_finitePastContinuousFuture (default : ContinuousPath alpha) :
    Measurable (finitePastContinuousFuture (index := index) (alpha := alpha) default) := by
  apply Measurable.prodMk
  · exact measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (Sum.inl i)
  · exact ContinuousPath.measurable_continuousExtension default |>.comp
      (measurable_pi_iff.mpr fun t ↦ measurable_pi_apply (Sum.inr t))

omit [MeasurableSpace alpha] [BorelSpace alpha]
  [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)] in
private theorem finitePastContinuousFuture_comp_finitePastDenseFuture
    (default : ContinuousPath alpha) :
    finitePastContinuousFuture (index := index) default ∘
        finitePastDenseFuture (index := index) (alpha := alpha) = id := by
  funext z
  apply Prod.ext
  · funext i
    rfl
  · exact ContinuousPath.continuousExtension_denseRestriction default z.2

/-- Two finite kernels on a finite-past/continuous-future space agree if every joint finite
coordinate restriction agrees.  The finite set may contain coordinates from both the past and
future summands; retaining only future coordinates would not determine their dependence. -/
theorem p2m_embedded_e1a647527eb6c1d2
    (default : ContinuousPath alpha)
    (kappa eta : Kernel beta ((index → alpha) × ContinuousPath alpha))
    [IsFiniteKernel kappa]
    (h : ∀ I : Finset (index ⊕ DenseTime),
      kappa.map (I.restrict ∘ finitePastDenseFuture) =
        eta.map (I.restrict ∘ finitePastDenseFuture)) :
    kappa = eta := by
  have hDense :
      kappa.map finitePastDenseFuture = eta.map finitePastDenseFuture := by
    apply _root_.MarkovProcess.Kernel.p2m_embedded_cf5a87fc6ca47934
    intro I
    rw [← Kernel.map_comp_right kappa measurable_finitePastDenseFuture
        (Finset.measurable_restrict I),
      ← Kernel.map_comp_right eta measurable_finitePastDenseFuture
        (Finset.measurable_restrict I)]
    exact h I
  calc
    kappa = (kappa.map finitePastDenseFuture).map
        (finitePastContinuousFuture (index := index) default) := by
      rw [← Kernel.map_comp_right]
      · rw [finitePastContinuousFuture_comp_finitePastDenseFuture, Kernel.map_id]
      · exact measurable_finitePastDenseFuture
      · exact measurable_finitePastContinuousFuture default
    _ = (eta.map finitePastDenseFuture).map
        (finitePastContinuousFuture (index := index) default) := by rw [hDense]
    _ = eta := by
      rw [← Kernel.map_comp_right]
      · rw [finitePastContinuousFuture_comp_finitePastDenseFuture, Kernel.map_id]
      · exact measurable_finitePastDenseFuture
      · exact measurable_finitePastContinuousFuture default

end
end Kernel
end MarkovProcess


