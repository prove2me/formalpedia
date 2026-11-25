-- Prove2me | Definitions.Def_SourceProof_42dda2460ed71edc7fce970c
-- name    : SourceProof_42dda2460ed71edc7fce970c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:03:12.418844+00:00
-- url     : https://prove2.me/theorems/168145ea-d268-5ca1-9a9e-1455cfa91d8a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stochasticIntegral_eq_pathStieltjesIntegral_on_finiteVariation

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticIntegral_F000
import Definitions.Def_SourceProof_08f35e40de15386d6fd32725
import Definitions.Def_SourceProof_30e6afddc12912a62054c909
import Definitions.Def_SourceProof_592358001a7c02aa8319b535
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_9183846313e90de3d6561ee0
import Definitions.Def_SourceProof_944fa57bc3b71053cbab118a
import Definitions.Def_SourceProof_a307e422895411519841ce97
import Definitions.Def_SourceProof_abb8e2f5680049693694a2fd
import Definitions.Def_SourceProof_b4ac9ec25a4681f709676503
import Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Protter II.18: local agreement on finite-variation sample paths

On one full-measure event, every finite-variation path of the integrator gives
the original pathwise Stieltjes integral. The finite-variation event need not
have full or positive probability, and no conditional measure or usualness for
a conditioned measure is assumed. The proof uses actual uniform subsequences.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_42dda2460ed71edc7fce970c
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    ∀ᵐ ω ∂P, ∀ hv : LocallyBoundedVariationOn (X · ω) univ,
      ∃ hωr : IsCadlagPath (X · ω), ∀ t,
        hX.stochasticIntegral hF ha hr t ω =
          pathStieltjesIntegral (X · ω) hv hωr.1 (H · ω) t := by
  obtain ⟨S, hS, huS⟩ := _root_.Prove2MeSourceProof.h_abb8e2f5680049693694a2fd ha hF hr
  have hJS := (_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hX) hF ha hr hS huS
  obtain ⟨k, hk, hkU⟩ := (_root_.Prove2MeSourceProof.h_944fa57bc3b71053cbab118a huS)
  obtain ⟨l, hl, hlU⟩ := (_root_.Prove2MeSourceProof.h_944fa57bc3b71053cbab118a ((_root_.Prove2MeSourceProof.h_a307e422895411519841ce97 hJS) hk.tendsto_atTop))
  filter_upwards [hkU, hlU, (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX), hr] with ω hSu hJu hXω hHω
  intro hv
  refine ⟨hXω, fun t ↦ ?_⟩
  have hs : TendstoUniformlyOn (fun n s ↦ S (k (l n)) s ω) (H · ω) atTop (Icc 0 t) :=
    _root_.Prove2MeSourceProof.h_9183846313e90de3d6561ee0.mp ((hSu t).comp hl.tendsto_atTop)
  have hi := _root_.Prove2MeSourceProof.h_592358001a7c02aa8319b535
    (fun n ↦ (_root_.Prove2MeSourceProof.h_b4ac9ec25a4681f709676503 ((_root_.Prove2MeSourceProof.h_08f35e40de15386d6fd32725 (hS (k (l n)))) ω)) hv hXω.1 t)
    ((_root_.Prove2MeSourceProof.h_b4ac9ec25a4681f709676503 hHω) hv hXω.1 t) hs
  have hj := (_root_.Prove2MeSourceProof.h_9183846313e90de3d6561ee0.mp (hJu t)).tendsto_at
    (show t ∈ Icc 0 t from ⟨bot_le, le_rfl⟩)
  change Tendsto (fun n ↦ (hS (k (l n))).elementaryIntegralProcess X t ω) atTop
    (𝓝 (hX.stochasticIntegral hF ha hr t ω)) at hj
  have heq (n : ℕ) : (hS (k (l n))).elementaryIntegralProcess X t ω =
      StochLean.pathStieltjesIntegral (X · ω) hv hXω.1 (S (k (l n)) · ω) t :=
    ((_root_.Prove2MeSourceProof.h_30e6afddc12912a62054c909 (hS (k (l n)))) hv hXω.1 t).symm
  simp only [heq] at hj
  exact tendsto_nhds_unique hj (hi.tendsto_at ⟨bot_le, le_rfl⟩)
end IsSemimartingale

end ProbabilityTheory


