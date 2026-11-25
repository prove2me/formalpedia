-- Prove2me | Definitions.Def_SourceProof_e8e88fba5b0d0c5182c1aea7
-- name    : SourceProof_e8e88fba5b0d0c5182c1aea7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:17:05.346356+00:00
-- url     : https://prove2.me/theorems/de00ffdc-d6a6-51a5-8926-b02f2346cc70
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.stoppingTimeReindex_of_ae_finite_usual

import Definitions.Def_StochLean_Probability_Process_Filtration_StoppingTimeReindex_F000
import Definitions.Def_SourceProof_4aad6e35fadea08fff8ce9d0
import Definitions.Def_SourceProof_cbee470a0aa2199fb74e9ccf

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Martingales sampled on ordered bounded stopping-time families

Each stopping time may have its own deterministic bound. This produces the genuine sampled
filtration, in contrast to the distinct theorem that stopping preserves the original filtration.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]
  {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
  [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

omit [SigmaFiniteFiltration P F] in

theorem _root_.Prove2MeSourceProof.h_e8e88fba5b0d0c5182c1aea7 (hX : Martingale X F P)
    (hu : UniformIntegrable X 1 P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (τ : ι → Ω → WithTop ℝ≥0) (hτ : ∀ i, IsStoppingTime F (τ i)) (hmono : Monotone τ)
    (hfinite : ∀ i, ∀ᵐ ω ∂P, τ i ω ≠ ⊤) :
    Martingale (fun i ↦ stoppedValue X (τ i)) (F.stoppingTimeReindex τ hτ hmono) P := by
  refine ⟨?_, fun i j hij ↦ ?_⟩
  · intro i
    exact ((_root_.Prove2MeSourceProof.h_4aad6e35fadea08fff8ce9d0 hX.stronglyAdapted) hF hr (hτ i)).stronglyMeasurable
  · exact ((_root_.Prove2MeSourceProof.h_cbee470a0aa2199fb74e9ccf hX) hu hF hr (hτ i) (hτ j)
      (ae_of_all _ (hmono hij)) (hfinite j)).symm
end MeasureTheory.Martingale


