-- Prove2me | Definitions.Def_PricingWithTips3DM_3e204cff19d090c0cf77322e
-- name    : PricingWithTips3DM_3e204cff19d090c0cf77322e
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:36:00.473302+00:00
-- url     : https://prove2.me/theorems/c24f8f6d-919f-4d56-995d-b107662ad990
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_498bba7a490a84d9a63ab0be
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# General CLIQUE encoding facade

Imports the canonical encoders, complete parsers, and their round-trip laws.
-/


