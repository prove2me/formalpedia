-- Prove2me | Definitions.Def_SourceProof_d5b15f96b9cae3c9fe969458
-- name    : SourceProof_d5b15f96b9cae3c9fe969458
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:05:53.506974+00:00
-- url     : https://prove2.me/theorems/4353717c-df65-5d03-956b-a02ebf5599db
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLocalMartingale.isUIMartingale_of_bound

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Definitions.Def_SourceProof_260b5df8ab262ee944da176f
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

namespace IsLocalMartingale
theorem _root_.Prove2MeSourceProof.h_d5b15f96b9cae3c9fe969458 [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
    (hX : IsLocalMartingale X F P) (C : ℝ≥0)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ C) : IsUIMartingale X F P :=
  (_root_.Prove2MeSourceProof.h_260b5df8ab262ee944da176f hX) (integrable_const (C : ℝ)) hb
end IsLocalMartingale

end ProbabilityTheory


