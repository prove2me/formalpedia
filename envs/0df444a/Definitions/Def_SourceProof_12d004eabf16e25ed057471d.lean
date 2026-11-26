-- Prove2me | Definitions.Def_SourceProof_12d004eabf16e25ed057471d
-- name    : SourceProof_12d004eabf16e25ed057471d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T23:11:27.296528+00:00
-- url     : https://prove2.me/theorems/bf167617-999b-57e4-a71d-2b090f30f223
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stochasticIntegral_quadraticCovariation_eq

import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_3767d94c83301b280041ce3f
import Definitions.Def_SourceProof_3f47dd2e31d438d877ce48c9
import Definitions.Def_SourceProof_523d7cde826eec51d63a0e17
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_63e1469ea21d6ee826860dba
import Definitions.Def_SourceProof_707f7110645820b0d036c161
import Definitions.Def_SourceProof_7d09eb6a4e03c1fa37d5b869
import Definitions.Def_SourceProof_925a6c152cedf8b9c9d6d57e
import Definitions.Def_SourceProof_9a15eada3555a513322a1de0
import Definitions.Def_SourceProof_ba54eeb3a2661e253611936f
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Integrating the existing product formula

This identity uses the unique raw mixed bracket, integrator linearity and
associativity. The source initial terms are retained for arbitrary caglad H.
It does not yet identify the bracket of a stochastic integral.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_12d004eabf16e25ed057471d
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable
      (((_root_.Prove2MeSourceProof.h_9a15eada3555a513322a1de0 hX) hY hF).stochasticIntegral hF ha hr)
      (((_root_.Prove2MeSourceProof.h_ba54eeb3a2661e253611936f hX) hY hF).stochasticIntegral hF ha hr -
        hY.stochasticIntegral hF
          (fun t ↦ (ha t).mul
            ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX) t))
          ((_root_.Prove2MeSourceProof.h_523d7cde826eec51d63a0e17 hr) (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))) -
        hX.stochasticIntegral hF
          (fun t ↦ (ha t).mul
            ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hY)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY) t))
          ((_root_.Prove2MeSourceProof.h_523d7cde826eec51d63a0e17 hr) (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY)))) P := by
  let haX := (_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)
  let hrX := (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
  let haY := (_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hY)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY)
  let hrY := (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY))
  let hJY := (_root_.Prove2MeSourceProof.h_7d09eb6a4e03c1fa37d5b869 hY) hF haX hrX
  let hJX := (_root_.Prove2MeSourceProof.h_7d09eb6a4e03c1fa37d5b869 hX) hF haY hrY
  let hProd := (_root_.Prove2MeSourceProof.h_ba54eeb3a2661e253611936f hX) hY hF
  have hrep := _root_.Prove2MeSourceProof.h_3f47dd2e31d438d877ce48c9
    ((_root_.Prove2MeSourceProof.h_9a15eada3555a513322a1de0 hX) hY hF) ((_root_.Prove2MeSourceProof.h_63e1469ea21d6ee826860dba ((_root_.Prove2MeSourceProof.h_63e1469ea21d6ee826860dba hProd) hJY)) hJX) hF ha hr
      ((_root_.Prove2MeSourceProof.h_925a6c152cedf8b9c9d6d57e hX) hY hF)
  have hsub := (_root_.Prove2MeSourceProof.h_707f7110645820b0d036c161 ((_root_.Prove2MeSourceProof.h_63e1469ea21d6ee826860dba hProd) hJY)) hJX hF ha hr
  have hsub' := (_root_.Prove2MeSourceProof.h_707f7110645820b0d036c161 hProd) hJY hF ha hr
  have hassocY := (_root_.Prove2MeSourceProof.h_3767d94c83301b280041ce3f hY) hF ha hr haX hrX
  have hassocX := (_root_.Prove2MeSourceProof.h_3767d94c83301b280041ce3f hX) hF ha hr haY hrY
  filter_upwards [hrep, hsub, hsub', hassocY, hassocX] with ω he hs hs' hy hx t
  rw [he t, hs t]
  simp only [Pi.sub_apply, hs' t, hy t, hx t]
end IsSemimartingale

end ProbabilityTheory


