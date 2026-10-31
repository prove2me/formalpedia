-- Prove2me | Definitions.Def_MarkovProcess_V3H_Restart_RationalRestrictedRestart_3bd46ae7
-- name    : MarkovProcess_V3H_Restart_RationalRestrictedRestart_3bd46ae7
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:34:56.746563+00:00
-- url     : https://prove2.me/theorems/85949fdf-d198-4841-8216-2c2107e4da2e
-- title:
--   MarkovProcess: MarkovProcess_V3H_Restart_RationalRestrictedRestart_3bd46ae7
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_DenseFiltration_62a9879d
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Definitions.Def_MarkovProcess_V3H_Restart_RestrictedRestartOfJoint_e84e7ad8
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

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
theorem p2m_embedded_ba8c25b892b6b671 (S : DenseTime) (omega : ContinuousPath alpha) :
    densePastTerminal S (densePastRestriction S omega) =
      coordinateProcess (alpha := alpha) (DenseTime.castOrderEmbedding S) omega :=
  rfl

/-- A joint factorization of rational past and shifted future yields the restart identity after
restriction to every event in the canonical filtration at the rational terminal time. -/
theorem p2m_embedded_cb0825700818b2e6
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
  have hRestricted := _root_.MarkovProcess.p2m_embedded_95b5656d291c349f
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


