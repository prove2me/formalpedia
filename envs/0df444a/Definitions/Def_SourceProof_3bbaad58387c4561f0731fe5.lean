-- Prove2me | Definitions.Def_SourceProof_3bbaad58387c4561f0731fe5
-- name    : SourceProof_3bbaad58387c4561f0731fe5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:06:25.524705+00:00
-- url     : https://prove2.me/theorems/3ef1c875-28b4-4b5f-9359-d8786115e67f
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.jumpProcess_stochasticIntegral

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_9183846313e90de3d6561ee0
import Definitions.Def_SourceProof_944fa57bc3b71053cbab118a
import Definitions.Def_SourceProof_999b5f74151527fbcb6c58a5
import Definitions.Def_SourceProof_a307e422895411519841ce97
import Definitions.Def_SourceProof_ab0a4cce00e53a6efb5054a6
import Definitions.Def_SourceProof_abb8e2f5680049693694a2fd
import Definitions.Def_SourceProof_cfe916773aef5582e491259a
import Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e
import Definitions.Def_SourceProof_f4cb903591d31b9cb65eb02e

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Protter II.13: jumps of the constructed stochastic integral

Two actual subsequences give simultaneous locally uniform convergence of the
simple integrands and their integral processes on one full-measure event.
Uniform control also transfers strict-left limits, so the identity holds at all
times together, including the separate source jump at zero.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_3bbaad58387c4561f0731fe5
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable (jumpProcess (hX.stochasticIntegral hF ha hr))
      (fun t ω ↦ H t ω * jumpProcess X t ω) P := by
  obtain ⟨S, hS, huS⟩ := _root_.Prove2MeSourceProof.h_abb8e2f5680049693694a2fd ha hF hr
  have hJS := (_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hX) hF ha hr hS huS
  obtain ⟨k, hk, hkU⟩ := (_root_.Prove2MeSourceProof.h_944fa57bc3b71053cbab118a huS)
  obtain ⟨l, hl, hlU⟩ := (_root_.Prove2MeSourceProof.h_944fa57bc3b71053cbab118a ((_root_.Prove2MeSourceProof.h_a307e422895411519841ce97 hJS) hk.tendsto_atTop))
  filter_upwards [hkU, hlU, (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)] with ω hSu hJu hXω
  intro t
  have hs : Tendsto (fun n ↦ S (k (l n)) t ω) atTop (𝓝 (H t ω)) :=
    ((_root_.Prove2MeSourceProof.h_9183846313e90de3d6561ee0.mp (hSu t)).tendsto_at
      ⟨bot_le, le_rfl⟩).comp hl.tendsto_atTop
  have hj : Tendsto (fun n ↦ ProbabilityTheory.jumpProcess ((hS (k (l n))).elementaryIntegralProcess X) t ω)
      atTop (𝓝 (ProbabilityTheory.jumpProcess (hX.stochasticIntegral hF ha hr) t ω)) :=
    _root_.Prove2MeSourceProof.h_999b5f74151527fbcb6c58a5
      (fun n ↦ (_root_.Prove2MeSourceProof.h_cfe916773aef5582e491259a (hS (k (l n)))) hXω)
      ((_root_.Prove2MeSourceProof.h_ab0a4cce00e53a6efb5054a6 hX) hF ha hr ω)
      (_root_.Prove2MeSourceProof.h_9183846313e90de3d6561ee0.mp (hJu t))
  simp only [_root_.Prove2MeSourceProof.h_f4cb903591d31b9cb65eb02e _ hXω] at hj
  exact tendsto_nhds_unique hj (hs.mul_const (ProbabilityTheory.jumpProcess X t ω))
end IsSemimartingale

end ProbabilityTheory


