-- Prove2me | Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part9
-- name    : PricingWithTips3DM_3a64b523d21161fe1251d130Part9
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T08:22:39.936912+00:00
-- url     : https://prove2.me/theorems/dfe5e054-b080-43c9-b2ee-c7e890d6d735
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShape3DM.Part9
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part8
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

namespace PricingWithTips.FixedShape3DM

open Hardness Hardness.Cert Hardness.Sat3dm

theorem threeDM_np_hard_of_reduction_polytime
    (hreduction : Nonempty (Turing.TM2ComputableInPolyTime
      (id : List CLRS.Chapter34.CNFSym → List CLRS.Chapter34.CNFSym)
      encodeThreeDMInstance reduction)) :
    NPHardMarketPredicate ThreeDMYes := by
  intro Γ L hL
  obtain ⟨f, hf, hcorrect⟩ :=
    CLRS3DM.clrs_threeCNFSat_npHard Γ L
      (CLRS3DM.polynomiallyVerifiable_to_CLRS hL)
  refine ⟨reduction ∘ f, ?_, ?_⟩
  · exact CLRS.Chapter34.PolyTimeComputable.comp hf hreduction
  · intro x
    exact (hcorrect x).trans (reduction_correct (f x))
end PricingWithTips.FixedShape3DM


