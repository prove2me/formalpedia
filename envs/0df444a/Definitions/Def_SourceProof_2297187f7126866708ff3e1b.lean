-- Prove2me | Definitions.Def_SourceProof_2297187f7126866708ff3e1b
-- name    : SourceProof_2297187f7126866708ff3e1b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:03:01.957557+00:00
-- url     : https://prove2.me/theorems/71ddbb11-b741-5b95-ac9c-b9a941137272
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.hasLocallyIntegrableVariation_largeJumpSumProcesses

import Definitions.Def_SourceProof_264b430747bbe6ee020dbafc
import Definitions.Def_SourceProof_291f8623e29c3647f4304312
import Definitions.Def_SourceProof_4cb05f474a070d71055c9fca
import Definitions.Def_SourceProof_5df5dbd8f904218dccc01cab
import Definitions.Def_SourceProof_ad0813405a39769f6af6bc1c
import Definitions.Def_SourceProof_ae0266e80e099d3f3f27bbad
import Definitions.Def_SourceProof_f27f0406d0856e73dc290674

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual locally integrable variation of a martingale's large jumps

The joint capped exits of the cumulative norm sum plus the source norm have
an overshoot controlled by the original martingale's actual bounded stopping
sample. Optional sampling makes that envelope integrable. This proves finite
expected variation of the actual stopped signed and norm sums, with variation
finiteness and measurability established before any real conversion.

Only a true cadlag martingale is required here, not uniform integrability,
bounded source values, square integrability, or a semimartingale witness.
The initial random value need not vanish. The local-martingale extension is
a separate native localization argument.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {b : ℝ}


theorem _root_.Prove2MeSourceProof.h_2297187f7126866708ff3e1b
    (hX : Martingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) (hb : 0 < b) :
    HasLocallyIntegrableVariation (largeJumpSumProcess X b) F P ∧
      HasLocallyIntegrableVariation (largeJumpNormSumProcess X b) F P := by
  let Z : ℝ≥0 → Ω → ℝ := fun t ω ↦ ProbabilityTheory.largeJumpNormSumProcess X b t ω + ‖X t ω‖
  have haX := hX.stronglyAdapted.adapted
  have haC := ((_root_.Prove2MeSourceProof.h_291f8623e29c3647f4304312 haX) hF hc hb).2
  have hcC := ((_root_.Prove2MeSourceProof.h_4cb05f474a070d71055c9fca hc) hb).2.1
  have haZ : Adapted F Z := by
    intro t
    let : MeasurableSpace Ω := F t
    exact (haC t).measurable.add (haX t).norm
  have hcZ : ProbabilityTheory.HasCadlagPaths Z P := (_root_.Prove2MeSourceProof.h_f27f0406d0856e73dc290674 hcC) ((_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc hc) continuous_norm)
  have hτ := (_root_.Prove2MeSourceProof.h_5df5dbd8f904218dccc01cab haZ) hF hcZ
  exact ⟨_root_.Prove2MeSourceProof.h_ae0266e80e099d3f3f27bbad.mpr
      ⟨ProbabilityTheory.cappedNormExitSequence Z, hτ, fun n ↦
        ((_root_.Prove2MeSourceProof.h_ad0813405a39769f6af6bc1c hX) hF hc hb n).1⟩,
    _root_.Prove2MeSourceProof.h_ae0266e80e099d3f3f27bbad.mpr
      ⟨ProbabilityTheory.cappedNormExitSequence Z, hτ, fun n ↦
        ((_root_.Prove2MeSourceProof.h_ad0813405a39769f6af6bc1c hX) hF hc hb n).2⟩⟩
end MeasureTheory.Martingale


