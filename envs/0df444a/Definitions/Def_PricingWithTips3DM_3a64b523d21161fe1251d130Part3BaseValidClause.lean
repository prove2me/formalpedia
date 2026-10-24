-- Prove2me | Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseValidClause
-- name    : PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseValidClause
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T07:43:15.791337+00:00
-- url     : https://prove2.me/theorems/472a8260-0723-4546-89f1-53fe9918ca0f
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShape3DM.Part3.Base.Valid.Clause
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
namespace PricingWithTips.FixedShape3DM
open Hardness Hardness.Cert Hardness.Sat3dm

theorem baseCNF_clause_witness (input : List CLRS.Chapter34.CNFSym)
    (h : CLRS.Chapter34.isThreeCNFBool
      (CLRS.Chapter34.decodeCNF input) = true)
    {c : Hardness.Clause ℕ} (hc : c ∈ baseCNF input) :
    ∃ clause ∈ CLRS.Chapter34.decodeCNF input,
      c = (clause.map CLRS3CNFBridge.certLiteral).map
        Hardness.Cert.litOf := by
  unfold baseCNF at hc
  simp only [CLRS3CNFBridge.guardedCertCNF, h, if_true,
    Hardness.Cert.decodeCNF, CLRS3CNFBridge.certCNF,
    List.mem_map] at hc
  obtain ⟨encoded, hencoded, rfl⟩ := hc
  obtain ⟨clause, hclause, rfl⟩ := hencoded
  exact ⟨clause, hclause, rfl⟩

end PricingWithTips.FixedShape3DM


