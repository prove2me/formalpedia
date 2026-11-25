-- Prove2me | Definitions.Def_SourceProof_c597cf6ac1143ac927f99acf
-- name    : SourceProof_c597cf6ac1143ac927f99acf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:36:28.835274+00:00
-- url     : https://prove2.me/theorems/c9d8dcf6-63fc-5bc7-85b0-6ecf72ea514d
-- title:
--   StochLean source theorem: ProbabilityTheory.NonnegativeLevyPair.isLevyMeasure_jumpMeasure

import Definitions.Def_SourceProof_10bc21c181b2694ed4b3240e
import Definitions.Def_SourceProof_61527dde036c91b88ebdd404
import Definitions.Def_SourceProof_c3e069bf138852082f57b309

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

theorem _root_.Prove2MeSourceProof.h_c597cf6ac1143ac927f99acf (η : NonnegativeLevyPair) :
    IsLevyMeasure η.jumpMeasure := by
  refine ⟨(_root_.Prove2MeSourceProof.h_10bc21c181b2694ed4b3240e η), ?_⟩
  have hbound : ∀ᵐ x ∂η.jumpMeasure,
      ProbabilityTheory.levyIntegrand x ≤ ENNReal.ofReal (min 1 x) := by
    filter_upwards [η.supportedPositive] with x hx
    by_cases hsmall : x < 1
    · have habs : |x| < 1 := by simpa [abs_of_pos hx] using hsmall
      rw [_root_.Prove2MeSourceProof.h_c3e069bf138852082f57b309 habs, min_eq_right hsmall.le]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
    · have hone : 1 ≤ |x| := by simpa [abs_of_pos hx] using le_of_not_gt hsmall
      rw [_root_.Prove2MeSourceProof.h_61527dde036c91b88ebdd404 hone, min_eq_left (le_of_not_gt hsmall)]
      norm_num
  have hlin : ∫⁻ x, ENNReal.ofReal (min 1 x) ∂η.jumpMeasure < ∞ := by
    have hi := (hasFiniteIntegral_iff_norm (fun x : ℝ ↦ min 1 x)).mp
      η.integrable_min_one.hasFiniteIntegral
    convert hi using 1
    apply lintegral_congr_ae
    filter_upwards [η.supportedPositive] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (lt_min zero_lt_one hx)]
  exact lt_of_le_of_lt (lintegral_mono_ae hbound) hlin
end NonnegativeLevyPair
end ProbabilityTheory


