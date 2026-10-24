-- Prove2me | Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part8
-- name    : PricingWithTips3DM_3a64b523d21161fe1251d130Part8
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T08:18:23.205491+00:00
-- url     : https://prove2.me/theorems/48f5e425-509f-4db2-b94d-3c98c89922c8
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShape3DM.Part8
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part7
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

namespace PricingWithTips.FixedShape3DM

open Hardness Hardness.Cert Hardness.Sat3dm

theorem reduction_correct (input : List CLRS.Chapter34.CNFSym) :
    input ∈ CLRS.Chapter34.ThreeCNFSat ↔ ThreeDMYes (reduction input) := by
  calc
    input ∈ CLRS.Chapter34.ThreeCNFSat ↔ (paddedCNF input).Satisfiable :=
      threeCNFSat_iff_paddedCNF input
    _ ↔ MATCHING_3D (abstractInstance input) := by
      exact satisfiable_iff_matching input
    _ ↔ MATCHING_3D (normalizedInstance input) := matching_normalized_iff input
    _ ↔ HasPerfectFinset3DM (dimension input) (normalizedTriples input) := Iff.rfl
    _ ↔ HasPerfect3DMatching (dimension input)
        (fun b s d => decide ((b, s, d) ∈ normalizedTriples input)) :=
      PricingWithTips.finset3DM_iff_allocation3DM _ _
    _ ↔ ThreeDMYes (reduction input) := Iff.rfl
end PricingWithTips.FixedShape3DM


