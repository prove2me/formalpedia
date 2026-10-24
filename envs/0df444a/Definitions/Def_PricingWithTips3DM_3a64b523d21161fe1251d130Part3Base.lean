-- Prove2me | Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3Base
-- name    : PricingWithTips3DM_3a64b523d21161fe1251d130Part3Base
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T07:50:00.821979+00:00
-- url     : https://prove2.me/theorems/0d5e2e7c-5c10-48f0-9cbb-e869ea9ae461
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShape3DM.Part3.Base
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseValid
import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseInvalid
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
namespace PricingWithTips.FixedShape3DM
open Hardness Hardness.Cert Hardness.Sat3dm

theorem baseCNF_variable_coverage (input : List CLRS.Chapter34.CNFSym)
    {c : Hardness.Clause ℕ} (hc : c ∈ baseCNF input)
    {l : Hardness.Literal ℕ} (hl : l ∈ c) :
    l.var ∈ variableList input := by
  by_cases h : CLRS.Chapter34.isThreeCNFBool
      (CLRS.Chapter34.decodeCNF input) = true
  · exact baseCNF_variable_coverage_valid input h hc hl
  · exact baseCNF_variable_coverage_invalid input h hc hl

end PricingWithTips.FixedShape3DM


