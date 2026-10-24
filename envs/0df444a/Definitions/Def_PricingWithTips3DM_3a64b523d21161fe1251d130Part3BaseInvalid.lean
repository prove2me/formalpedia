-- Prove2me | Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseInvalid
-- name    : PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseInvalid
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T07:07:33.108078+00:00
-- url     : https://prove2.me/theorems/c82a1590-556d-4911-9828-77645b6ff943
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShape3DM.Part3.Base.Invalid
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
namespace PricingWithTips.FixedShape3DM
open Hardness Hardness.Cert Hardness.Sat3dm

theorem baseCNF_variable_coverage_invalid (input : List CLRS.Chapter34.CNFSym)
    (h : CLRS.Chapter34.isThreeCNFBool
      (CLRS.Chapter34.decodeCNF input) ≠ true)
    {c : Hardness.Clause ℕ} (hc : c ∈ baseCNF input)
    {l : Hardness.Literal ℕ} (hl : l ∈ c) :
    l.var ∈ variableList input := by
  unfold baseCNF at hc
  have : c = [] := by
    simpa [CLRS3CNFBridge.guardedCertCNF, h,
      Hardness.Cert.decodeCNF] using hc
  subst c
  simp at hl

end PricingWithTips.FixedShape3DM


