-- Prove2me | Definitions.Def_SourceProof_d2b77a9c3200634f142d37a0
-- name    : SourceProof_d2b77a9c3200634f142d37a0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:06:39.895595+00:00
-- url     : https://prove2.me/theorems/108bc323-a10d-4139-a56f-5f1183bf9e65
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stochasticIntegral_zero_ae

import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticIntegral_F000
import Definitions.Def_SourceProof_683160b98a33817cd725c918
import Definitions.Def_SourceProof_9183846313e90de3d6561ee0
import Definitions.Def_SourceProof_944fa57bc3b71053cbab118a
import Definitions.Def_SourceProof_a307e422895411519841ce97
import Definitions.Def_SourceProof_abb8e2f5680049693694a2fd
import Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The source initial term of the constructed integral

The integral starts at `H_0 X_0`, with no integrability or boundedness assumption
on either factor. Actual almost-sure subsequences transfer the elementary identity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_d2b77a9c3200634f142d37a0
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    hX.stochasticIntegral hF ha hr 0 =ᵐ[P] fun ω ↦ H 0 ω * X 0 ω := by
  obtain ⟨S, hS, huS⟩ := _root_.Prove2MeSourceProof.h_abb8e2f5680049693694a2fd ha hF hr
  have hJS := (_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hX) hF ha hr hS huS
  obtain ⟨k, hk, hkU⟩ := (_root_.Prove2MeSourceProof.h_944fa57bc3b71053cbab118a huS)
  obtain ⟨l, hl, hlU⟩ := (_root_.Prove2MeSourceProof.h_944fa57bc3b71053cbab118a ((_root_.Prove2MeSourceProof.h_a307e422895411519841ce97 hJS) hk.tendsto_atTop))
  filter_upwards [hkU, hlU] with ω hSu hJu
  have hs : Tendsto (fun n ↦ S (k (l n)) 0 ω) atTop (𝓝 (H 0 ω)) :=
    ((_root_.Prove2MeSourceProof.h_9183846313e90de3d6561ee0.mp (hSu 0)).tendsto_at
      ⟨le_rfl, le_rfl⟩).comp hl.tendsto_atTop
  have hj : Tendsto (fun n ↦ (hS (k (l n))).elementaryIntegralProcess X 0 ω) atTop
      (𝓝 (hX.stochasticIntegral hF ha hr 0 ω)) :=
    (_root_.Prove2MeSourceProof.h_9183846313e90de3d6561ee0.mp (hJu 0)).tendsto_at ⟨le_rfl, le_rfl⟩
  simp only [_root_.Prove2MeSourceProof.h_683160b98a33817cd725c918] at hj
  exact tendsto_nhds_unique hj (hs.mul_const (X 0 ω))
end IsSemimartingale

end ProbabilityTheory


