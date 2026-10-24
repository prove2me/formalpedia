-- Prove2me | Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3
-- name    : PricingWithTips3DM_3a64b523d21161fe1251d130Part3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T07:53:01.138041+00:00
-- url     : https://prove2.me/theorems/dfbdf2ac-cc1f-4c8b-b44e-ad34fd85d026
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShape3DM.Part3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3Base
import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3Padding
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
namespace PricingWithTips.FixedShape3DM
open Hardness Hardness.Cert Hardness.Sat3dm

theorem variable_coverage (input : List CLRS.Chapter34.CNFSym) :
    ∀ c ∈ paddedCNF input, ∀ l ∈ c, l.var ∈ variableList input := by
  intro c hc l hl
  rw [paddedCNF, List.mem_append] at hc
  rcases hc with hc | hc
  · exact baseCNF_variable_coverage input hc hl
  · exact padding_variable_coverage input hc hl

end PricingWithTips.FixedShape3DM


