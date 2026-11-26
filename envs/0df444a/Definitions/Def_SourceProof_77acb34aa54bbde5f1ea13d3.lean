-- Prove2me | Definitions.Def_SourceProof_77acb34aa54bbde5f1ea13d3
-- name    : SourceProof_77acb34aa54bbde5f1ea13d3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T22:58:25.60393+00:00
-- url     : https://prove2.me/theorems/32111b71-a9ce-4f16-9e73-a33873f40ccd
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLocalMartingale.hasLocallyIntegrableVariation_largeJumpSumProcesses

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_LocallyIntegrableLocalization_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_2297187f7126866708ff3e1b
import Definitions.Def_SourceProof_291f8623e29c3647f4304312
import Definitions.Def_SourceProof_362f6277c2a889bfdf4decbb
import Definitions.Def_SourceProof_4cb05f474a070d71055c9fca
import Definitions.Def_SourceProof_7e41a7708f0759111a0ce622
import Definitions.Def_SourceProof_adff851f13316a352bc1b23e
import Definitions.Def_SourceProof_b9fa7849de713fb134f04028
import Definitions.Def_SourceProof_dc984e4bcf546833c944556d
import Definitions.Def_SourceProof_e0cb3dd1b2f9a2e13af44d99
import Definitions.Def_SourceProof_e5cd06173d05191672a576c7
import Definitions.Def_SourceProof_fbe511cab72102196d05a325

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Locally integrable large-jump sums of a local martingale

The original fundamental sequence gives true martingales after positive-lifetime
masking and stopping. Their actual signed and norm large-jump sums have locally
integrable variation by the true-martingale result. Exact event restriction and
the common-event stopped-sum identity identify these with the native masked
stoppings of the original sums. Stable-bundle localization idempotence then
gives locally integrable variation of those original cumulative processes.

No semimartingale representation, new localizing selector, source moment bound,
or integrability of the initial random value is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

namespace IsLocalMartingale

theorem _root_.Prove2MeSourceProof.h_77acb34aa54bbde5f1ea13d3
    (hM : IsLocalMartingale X F P) (hF : F.IsUsual P) (hb : 0 < b) :
    HasLocallyIntegrableVariation (largeJumpSumProcess X b) F P ∧
      HasLocallyIntegrableVariation (largeJumpNormSumProcess X b) F P := by
  obtain ⟨haA, haC⟩ := (_root_.Prove2MeSourceProof.h_291f8623e29c3647f4304312 hM.1) hF hM.2.1 hb
  obtain ⟨hcA, hcC, _⟩ := (_root_.Prove2MeSourceProof.h_4cb05f474a070d71055c9fca hM.2.1) hb
  obtain ⟨τ, hτ⟩ := hM.2.2
  have hlocal (n : ℕ) :
      ProbabilityTheory.HasLocallyIntegrableVariation (MeasureTheory.stoppedProcess
        (fun t ↦ {ω | 0 < τ n ω}.indicator (ProbabilityTheory.largeJumpSumProcess X b t)) (τ n)) F P ∧
      ProbabilityTheory.HasLocallyIntegrableVariation (MeasureTheory.stoppedProcess
        (fun t ↦ {ω | 0 < τ n ω}.indicator (ProbabilityTheory.largeJumpNormSumProcess X b t)) (τ n)) F P := by
    have hcMask := (_root_.Prove2MeSourceProof.h_7e41a7708f0759111a0ce622 hM.2.1) {ω | 0 < τ n ω}
    have hv := (_root_.Prove2MeSourceProof.h_2297187f7126866708ff3e1b (hτ.2.2 n).1)
      hF ((_root_.Prove2MeSourceProof.h_1557efb7e848f4cf57c0170c hcMask) (τ n)) hb
    have heA := (_root_.Prove2MeSourceProof.h_fbe511cab72102196d05a325 hcMask) b (τ n)
    have heC := (_root_.Prove2MeSourceProof.h_dc984e4bcf546833c944556d hcMask) b (τ n)
    rw [_root_.Prove2MeSourceProof.h_e5cd06173d05191672a576c7] at heA
    rw [_root_.Prove2MeSourceProof.h_e0cb3dd1b2f9a2e13af44d99] at heC
    exact ⟨(_root_.Prove2MeSourceProof.h_b9fa7849de713fb134f04028 hv.1) heA, (_root_.Prove2MeSourceProof.h_b9fa7849de713fb134f04028 hv.2) heC⟩
  exact ⟨_root_.Prove2MeSourceProof.h_362f6277c2a889bfdf4decbb hF haA.adapted hcA
      ⟨τ, (_root_.Prove2MeSourceProof.h_adff851f13316a352bc1b23e hτ), fun n ↦ (hlocal n).1⟩,
    _root_.Prove2MeSourceProof.h_362f6277c2a889bfdf4decbb hF haC.adapted hcC
      ⟨τ, (_root_.Prove2MeSourceProof.h_adff851f13316a352bc1b23e hτ), fun n ↦ (hlocal n).2⟩⟩
end IsLocalMartingale

end ProbabilityTheory


