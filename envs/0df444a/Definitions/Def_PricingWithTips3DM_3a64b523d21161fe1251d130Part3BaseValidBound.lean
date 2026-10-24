-- Prove2me | Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseValidBound
-- name    : PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseValidBound
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T07:27:08.318995+00:00
-- url     : https://prove2.me/theorems/c01d1fc1-6283-407d-a9b6-6482a96bb1ae
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShape3DM.Part3.Base.Valid.Bound
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
namespace PricingWithTips.FixedShape3DM
open Hardness Hardness.Cert Hardness.Sat3dm

theorem certified_literal_variable_lt (input : List CLRS.Chapter34.CNFSym)
    {clause : CLRS.Chapter34.Clause}
    (hclause : clause ∈ CLRS.Chapter34.decodeCNF input)
    {literal : CLRS.Chapter34.Literal} (hliteral : literal ∈ clause) :
    (Hardness.Cert.litOf
      (CLRS3CNFBridge.certLiteral literal)).var < input.length := by
  have hbound := CLRS.Chapter34.decodeCNF_indices_lt
    input clause hclause literal hliteral
  cases literal <;> simpa [Hardness.Cert.litOf,
    CLRS3CNFBridge.certLiteral, CLRS.Chapter34.litIndex] using hbound

end PricingWithTips.FixedShape3DM


