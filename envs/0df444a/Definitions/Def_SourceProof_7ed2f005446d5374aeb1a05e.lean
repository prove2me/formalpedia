-- Prove2me | Definitions.Def_SourceProof_7ed2f005446d5374aeb1a05e
-- name    : SourceProof_7ed2f005446d5374aeb1a05e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:41:47.942802+00:00
-- url     : https://prove2.me/theorems/d2670b0a-cb7d-4c45-a063-d05a430c767d
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.integrable_stoppedValue_of_bounded

import Definitions.Def_StochLean_Probability_Martingale_OptionalSampling_ContinuousTime_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Definitions.Def_SourceProof_abd730752414d0d67e6d98a8

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Stopping continuous-time martingales

The bounded optional-sampling theorem is transported to Mathlib's canonical
`WithTop`-valued stopping times. Splitting on the ordering of two stopping times
then gives the minimum formula. In particular a stopped martingale is a
martingale for the original filtration, not merely the stopped filtration.

Source: Protter I.17 and the corollary of I.18. The unrestricted UI conclusion
of I.18 additionally needs the unbounded optional-sampling theorem.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem _root_.Prove2MeSourceProof.h_7ed2f005446d5374aeb1a05e (hX : Martingale X F P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hbound : ∀ ω, τ ω ≤ T) : Integrable (stoppedValue X τ) P :=
  integrable_condExp.congr ((_root_.Prove2MeSourceProof.h_abd730752414d0d67e6d98a8 hX) hprog hr hτ hbound).symm
end MeasureTheory.Martingale


