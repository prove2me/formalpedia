-- Prove2me | Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseValid
-- name    : PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseValid
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T07:46:45.100693+00:00
-- url     : https://prove2.me/theorems/64e37b1f-9464-4c16-84d0-db5bc24dde7a
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShape3DM.Part3.Base.Valid
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseValidClause
import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseValidLiteral
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
namespace PricingWithTips.FixedShape3DM
open Hardness Hardness.Cert Hardness.Sat3dm

theorem baseCNF_variable_coverage_valid (input : List CLRS.Chapter34.CNFSym)
    (h : CLRS.Chapter34.isThreeCNFBool
      (CLRS.Chapter34.decodeCNF input) = true)
    {c : Hardness.Clause ℕ} (hc : c ∈ baseCNF input)
    {l : Hardness.Literal ℕ} (hl : l ∈ c) :
    l.var ∈ variableList input := by
  obtain ⟨clause, hclause, rfl⟩ := baseCNF_clause_witness input h hc
  exact converted_clause_variable_coverage input hclause hl

end PricingWithTips.FixedShape3DM


