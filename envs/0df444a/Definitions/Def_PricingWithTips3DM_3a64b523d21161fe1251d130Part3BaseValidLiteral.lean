-- Prove2me | Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseValidLiteral
-- name    : PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseValidLiteral
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T07:42:49.266093+00:00
-- url     : https://prove2.me/theorems/1a1d2095-5c32-4db7-af57-dc69bffbaed9
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShape3DM.Part3.Base.Valid.Literal
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseValidBound
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
namespace PricingWithTips.FixedShape3DM
open Hardness Hardness.Cert Hardness.Sat3dm

theorem converted_clause_variable_coverage
    (input : List CLRS.Chapter34.CNFSym)
    {clause : CLRS.Chapter34.Clause}
    (hclause : clause ∈ CLRS.Chapter34.decodeCNF input)
    {l : Hardness.Literal ℕ}
    (hl : l ∈ (clause.map CLRS3CNFBridge.certLiteral).map
      Hardness.Cert.litOf) :
    l.var ∈ variableList input := by
  simp only [List.mem_map] at hl
  obtain ⟨encoded, hencoded, rfl⟩ := hl
  obtain ⟨literal, hliteral, rfl⟩ := hencoded
  simpa [variableList] using
    certified_literal_variable_lt input hclause hliteral

end PricingWithTips.FixedShape3DM


