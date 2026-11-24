-- Prove2me | Definitions.Def_SourceProof_49a22f8c8626f92746c475a0
-- name    : SourceProof_49a22f8c8626f92746c475a0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:20.964599+00:00
-- url     : https://prove2.me/theorems/cef652f2-a922-4d64-9b98-31df0fbfd8b1
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPreLocalizingSequence.ae_eventually_masked_stoppedProcess_eq

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Dominated local martingales are martingales

The proof takes limits in the defining set-integral identities of the masked
fundamental sequence. Thus it does not require continuous-time optional
sampling or a semimartingale decomposition.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {τ : ℕ → Ω → WithTop ℝ≥0}

namespace IsPreLocalizingSequence

theorem _root_.Prove2MeSourceProof.h_49a22f8c8626f92746c475a0
    (hτ : IsPreLocalizingSequence F τ P) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      stoppedProcess (fun s ↦ {ω | 0 < τ n ω}.indicator (X s)) (τ n) t ω = X t ω := by
  filter_upwards [hτ.tendsto_top] with ω hω
  have he := hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))
  filter_upwards [he] with n hn
  have hpos : 0 < τ n ω := lt_of_le_of_lt bot_le hn
  rw [stoppedProcess_eq_of_le hn.le,
    indicator_of_mem (show ω ∈ {ω | 0 < τ n ω} from hpos)]
end IsPreLocalizingSequence

end ProbabilityTheory


