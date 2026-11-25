-- Prove2me | Definitions.Def_SourceProof_ad0813405a39769f6af6bc1c
-- name    : SourceProof_ad0813405a39769f6af6bc1c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:57:36.211633+00:00
-- url     : https://prove2.me/theorems/c20e7b1d-f5ea-5f1b-a9e1-89490e95fa13
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.hasIntegrableVariation_largeJumpSumProcesses_stopped_joint_exit

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_LocallyIntegrable_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_TerminalValue_F000
import Definitions.Def_SourceProof_07c7861230ad4c9ec462606c
import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_264b430747bbe6ee020dbafc
import Definitions.Def_SourceProof_291f8623e29c3647f4304312
import Definitions.Def_SourceProof_33622c9aa55480ec75c122c4
import Definitions.Def_SourceProof_33c8d48450307c7c064de424
import Definitions.Def_SourceProof_4cb05f474a070d71055c9fca
import Definitions.Def_SourceProof_6da37c641e8d3b5ccb3dfebc
import Definitions.Def_SourceProof_6e6c0736914066f88cc333e2
import Definitions.Def_SourceProof_72daf279aadd95bfbaff848c
import Definitions.Def_SourceProof_79df3f91a26f3a9f018e88d6
import Definitions.Def_SourceProof_7b2577ad98c1b05c2fcc98eb
import Definitions.Def_SourceProof_8721f78b0017a7455a9a15ba
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_c0529761b77dfaa59304baae
import Definitions.Def_SourceProof_c1f3beb58834c65ab1c84683
import Definitions.Def_SourceProof_d758c5fe1bf7eec6f7a3ad7f
import Definitions.Def_SourceProof_ef6d5d9fe54232ccd69dc8f3
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


theorem _root_.Prove2MeSourceProof.h_ad0813405a39769f6af6bc1c
    (hX : Martingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hb : 0 < b) (n : ℕ) :
    let τ := cappedNormExitSequence
      (fun t ω ↦ largeJumpNormSumProcess X b t ω + ‖X t ω‖) n
    HasIntegrableVariation (stoppedProcess (largeJumpSumProcess X b) τ) P ∧
      HasIntegrableVariation (stoppedProcess (largeJumpNormSumProcess X b) τ) P := by
  let A := ProbabilityTheory.largeJumpSumProcess X b
  let C := ProbabilityTheory.largeJumpNormSumProcess X b
  let Z : ℝ≥0 → Ω → ℝ := fun t ω ↦ C t ω + ‖X t ω‖
  let τ := ProbabilityTheory.cappedNormExitSequence Z n
  change ProbabilityTheory.HasIntegrableVariation (stoppedProcess A τ) P ∧
    ProbabilityTheory.HasIntegrableVariation (stoppedProcess C τ) P
  have haX := hX.stronglyAdapted.adapted
  obtain ⟨haA, haC⟩ := (_root_.Prove2MeSourceProof.h_291f8623e29c3647f4304312 haX) hF hc hb
  obtain ⟨hcA, hcC, _, hmC, hnC, hvAC⟩ := (_root_.Prove2MeSourceProof.h_4cb05f474a070d71055c9fca hc) hb
  have haZ : Adapted F Z := by
    intro t
    let : MeasurableSpace Ω := F t
    exact (haC t).measurable.add (haX t).norm
  have hcZ : ProbabilityTheory.HasCadlagPaths Z P := (_root_.Prove2MeSourceProof.h_f27f0406d0856e73dc290674 hcC) ((_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc hc) continuous_norm)
  have hτ : IsStoppingTime F τ := (_root_.Prove2MeSourceProof.h_6e6c0736914066f88cc333e2 haZ) hF hcZ n
  have hiX : Integrable (stoppedValue X τ) P :=
    (_root_.Prove2MeSourceProof.h_c0529761b77dfaa59304baae hX) hF (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c hc) hτ
      (_root_.Prove2MeSourceProof.h_ef6d5d9fe54232ccd69dc8f3 Z n)
  let G : Ω → ℝ := fun ω ↦ 2 * ((n + 1 : ℕ) : ℝ) + ‖stoppedValue X τ ω‖
  have hiG : Integrable G P := (integrable_const _).add hiX.norm
  have hnG (ω : Ω) : 0 ≤ G ω := by dsimp only [G]; positivity
  have heτ (ω : Ω) : ((τ ω).untopA : WithTop ℝ≥0) = τ ω := by
    rw [WithTop.untopA_eq_untop (_root_.Prove2MeSourceProof.h_33c8d48450307c7c064de424 Z n ω), WithTop.coe_untop]
  have hCBound : ∀ᵐ ω ∂P, ∀ t, 0 ≤ stoppedProcess C τ t ω ∧
      stoppedProcess C τ t ω ≤ G ω := by
    filter_upwards [hc, hnC] with ω hω hnω t
    refine ⟨hnω _, ?_⟩
    exact (_root_.Prove2MeSourceProof.h_72daf279aadd95bfbaff848c hω) hb n t
  have hC0 : stoppedProcess C τ 0 =ᵐ[P] 0 := by
    filter_upwards with ω
    rw [stoppedProcess_eq_of_le (u := C) (τ := τ) (i := (0 : ℝ≥0)) bot_le]
    exact congrFun (_root_.Prove2MeSourceProof.h_8721f78b0017a7455a9a15ba X b).2 ω
  have haCs := (_root_.Prove2MeSourceProof.h_d758c5fe1bf7eec6f7a3ad7f haC) hF (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c hcC) hτ
  have hvC : ProbabilityTheory.HasIntegrableVariation (stoppedProcess C τ) P :=
    ((_root_.Prove2MeSourceProof.h_07c7861230ad4c9ec462606c ((_root_.Prove2MeSourceProof.h_33622c9aa55480ec75c122c4 hmC) τ)) haCs.adapted hF
      ((_root_.Prove2MeSourceProof.h_1557efb7e848f4cf57c0170c hcC) τ) hC0 hiG hCBound).1
  have hvar : ∀ᵐ ω ∂P,
      eVariationOn (fun t ↦ stoppedProcess A τ t ω) univ ≤ ENNReal.ofReal (G ω) := by
    filter_upwards [hc, hvAC] with ω hω hvω
    rw [_root_.Prove2MeSourceProof.h_c1f3beb58834c65ab1c84683,
      _root_.Prove2MeSourceProof.h_6da37c641e8d3b5ccb3dfebc (_root_.Prove2MeSourceProof.h_33c8d48450307c7c064de424 Z n ω)]
    change eVariationOn (A · ω) (Icc 0 (τ ω).untopA) ≤ ENNReal.ofReal (G ω)
    exact (hvω (τ ω).untopA).trans (ENNReal.ofReal_le_ofReal
      ((_root_.Prove2MeSourceProof.h_7b2577ad98c1b05c2fcc98eb hω) hb (le_of_eq (heτ ω))))
  have hfin : ProbabilityTheory.HasFiniteTotalVariationPaths (stoppedProcess A τ) P :=
    hvar.mono fun _ hω ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω
  have haAs := (_root_.Prove2MeSourceProof.h_d758c5fe1bf7eec6f7a3ad7f haA) hF (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c hcA) hτ
  have hiV : Integrable (fun ω ↦
      (eVariationOn (fun t ↦ stoppedProcess A τ t ω) univ).toReal) P := by
    apply hiG.mono'
      ((_root_.Prove2MeSourceProof.h_79df3f91a26f3a9f018e88d6 haAs.adapted) hF
        ((_root_.Prove2MeSourceProof.h_1557efb7e848f4cf57c0170c hcA) τ)).ennreal_toReal.aestronglyMeasurable
    filter_upwards [hvar] with ω hω
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    simpa only [ENNReal.toReal_ofReal (hnG ω)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
  exact ⟨⟨hfin, hiV⟩, hvC⟩
end MeasureTheory.Martingale


