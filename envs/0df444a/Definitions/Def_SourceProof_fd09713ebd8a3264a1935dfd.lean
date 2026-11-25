-- Prove2me | Definitions.Def_SourceProof_fd09713ebd8a3264a1935dfd
-- name    : SourceProof_fd09713ebd8a3264a1935dfd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:27:22.00882+00:00
-- url     : https://prove2.me/theorems/7ca96c9b-a3d1-576b-af85-04e94ba83871
-- title:
--   StochLean source theorem: ProbabilityTheory.IsContinuousLocalMartingale.exists_bounded_klenkeLocalizingSequence

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_InitialValue_F000
import Definitions.Def_SourceProof_2c97b0da88fd3eb21715f5f0
import Definitions.Def_SourceProof_3e1f2415255d4696a3db025d
import Definitions.Def_SourceProof_d5b15f96b9cae3c9fe969458
import Definitions.Def_SourceProof_e79cc5d7fc8aa48d10e205ad
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bounded localization of continuous local martingales

Klenke 21.67 is used with its necessary initial-value guard. Closed-level hitting times of an
everywhere-continuous indistinguishable version give actual monotone localizers. The original
process is bounded after stopping on one common full-measure event, not just at fixed times.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

namespace IsContinuousLocalMartingale

theorem _root_.Prove2MeSourceProof.h_fd09713ebd8a3264a1935dfd
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) (C : ℝ≥0)
    (hzero : ∀ᵐ ω ∂P, ‖X 0 ω‖ ≤ C) :
    ∃ τ : ℕ → Ω → WithTop ℝ≥0, IsKlenkeLocalizingSequence X F P τ ∧
      ∀ n, (∀ᵐ ω ∂P, ∀ t, ‖MeasureTheory.stoppedProcess X (τ n) t ω‖ ≤ (C : ℝ) + n) ∧
        IsSquareIntegrableMartingale (MeasureTheory.stoppedProcess X (τ n)) F P := by
  obtain ⟨τ, hτ, hmono, hb⟩ := (_root_.Prove2MeSourceProof.h_3e1f2415255d4696a3db025d hX.1.1) hF hX.2 C hzero
  have hui : ∀ n, ProbabilityTheory.IsUIMartingale (MeasureTheory.stoppedProcess X (τ n)) F P := fun n ↦
    (_root_.Prove2MeSourceProof.h_d5b15f96b9cae3c9fe969458 ((_root_.Prove2MeSourceProof.h_2c97b0da88fd3eb21715f5f0 hX.1) hF (hτ.isStoppingTime n))) (C + n) (hb n)
  refine ⟨τ, ⟨hτ, hmono, hui⟩, fun n ↦ ⟨hb n, (hui n).1, ?_⟩⟩
  intro t
  exact MemLp.of_bound ((hui n).1.integrable t).aestronglyMeasurable ((C : ℝ) + n)
    ((hb n).mono fun _ hω ↦ hω t)
end IsContinuousLocalMartingale

end ProbabilityTheory


