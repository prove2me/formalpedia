-- Prove2me | Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3Padding
-- name    : PricingWithTips3DM_3a64b523d21161fe1251d130Part3Padding
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T06:58:54.256368+00:00
-- url     : https://prove2.me/theorems/de6cea12-1bf5-48ce-9bc4-fb99b08d1248
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShape3DM.Part3.Padding
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
namespace PricingWithTips.FixedShape3DM
open Hardness Hardness.Cert Hardness.Sat3dm

theorem padding_variable_coverage (input : List CLRS.Chapter34.CNFSym)
    {c : Hardness.Clause ℕ}
    (hc : c ∈ List.replicate (input.length - (baseCNF input).length) tautClause)
    {l : Hardness.Literal ℕ} (hl : l ∈ c) :
    l.var ∈ variableList input := by
  have hc' : c = tautClause := by simpa using List.eq_of_mem_replicate hc
  subst c
  have hpos : 0 < input.length := by
    have hle := baseCNF_length_le input
    have hrep : 0 < input.length - (baseCNF input).length := by
      simpa using List.length_pos_of_mem hc
    omega
  simp [tautClause] at hl
  rcases hl with rfl | rfl <;> simpa [variableList] using hpos

end PricingWithTips.FixedShape3DM


