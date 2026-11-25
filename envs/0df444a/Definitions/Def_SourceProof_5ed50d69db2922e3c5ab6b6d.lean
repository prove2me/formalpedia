-- Prove2me | Definitions.Def_SourceProof_5ed50d69db2922e3c5ab6b6d
-- name    : SourceProof_5ed50d69db2922e3c5ab6b6d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:49:33.195933+00:00
-- url     : https://prove2.me/theorems/edf2bdcf-307f-45d4-bee4-793bbf403433
-- title:
--   StochLean source theorem: ProbabilityTheory.NonnegativeLevyPair.isNonnegativeLaw_finiteRestrictionLaw

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F023
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_NonnegativeLevyKhintchine_F001
import Definitions.Def_SourceProof_178e43959bf59fc48ea08b6a
import Definitions.Def_SourceProof_1fe64fee2b70f64733db8bf1
import Definitions.Def_SourceProof_21f040e5ec5495fe7abf1831
import Definitions.Def_SourceProof_594405e958b8c344babc33a9
import Definitions.Def_SourceProof_c470c86e8dae14cf9182aec5
import Definitions.Def_SourceProof_d332d56749c842e62ff71033

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Nonnegative Levy--Khintchine parameters

The canonical parameters of a subordinator consist of a nonnegative deterministic part and a
positive jump measure integrating `min 1 x`.  This file embeds those parameters into StochLean's
fixed-truncation real Levy triplets and proves the constructive half of the nonnegative
Levy--Khintchine theorem, including nonnegative support of the resulting law.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace ProbabilityTheory

namespace NonnegativeLevyPair

theorem _root_.Prove2MeSourceProof.h_5ed50d69db2922e3c5ab6b6d (η : NonnegativeLevyPair) (n : ℕ) :
    (η.toLevyTriplet.finiteRestrictionLaw n).IsNonnegativeLaw := by
  let ξ := (ProbabilityTheory.NonnegativeLevyPair.toLevyTriplet η).finiteRestriction n
  letI : IsFiniteMeasure ξ.jumpMeasure :=
    (_root_.Prove2MeSourceProof.h_594405e958b8c344babc33a9 (ProbabilityTheory.NonnegativeLevyPair.toLevyTriplet η)) n
  change (ξ.finiteJumpLaw).IsNonnegativeLaw
  change MeasureTheory.ProbabilityMeasure.IsNonnegativeLaw
    (MeasureTheory.ProbabilityMeasure.conv
      (MeasureTheory.ProbabilityMeasure.conv
        (MeasureTheory.ProbabilityMeasure.pointMass
          (ξ.drift - ∫ x, ProbabilityTheory.levyTruncation x ∂ξ.jumpMeasure))
        (ProbabilityTheory.LevyTriplet.gaussianLaw 0 ξ.gaussianVariance))
      (ProbabilityTheory.CompoundPoisson.ofFiniteMeasure
        (⟨ξ.jumpMeasure, inferInstance⟩ : FiniteMeasure ℝ)))
  apply _root_.Prove2MeSourceProof.h_21f040e5ec5495fe7abf1831
  · apply _root_.Prove2MeSourceProof.h_21f040e5ec5495fe7abf1831
    · rw [_root_.Prove2MeSourceProof.h_d332d56749c842e62ff71033]
      have hle := (_root_.Prove2MeSourceProof.h_178e43959bf59fc48ea08b6a η) n
      have hd : 0 ≤ (η.deterministicPart : ℝ) := NNReal.coe_nonneg _
      dsimp [ξ, ProbabilityTheory.LevyTriplet.finiteRestriction, ProbabilityTheory.NonnegativeLevyPair.toLevyTriplet]
      push_cast
      linarith
    · rw [show ξ.gaussianVariance = 0 by rfl, _root_.Prove2MeSourceProof.h_1fe64fee2b70f64733db8bf1]
      exact (_root_.Prove2MeSourceProof.h_d332d56749c842e62ff71033 0).2 le_rfl
  · apply _root_.Prove2MeSourceProof.h_c470c86e8dae14cf9182aec5
    exact ae_restrict_of_ae (η.supportedPositive.mono fun x hx ↦ hx.le)
end NonnegativeLevyPair
end ProbabilityTheory


