-- Prove2me | Definitions.Def_PricingWithTips3DM_73463e9c86d4d084282cdafd
-- name    : PricingWithTips3DM_73463e9c86d4d084282cdafd
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:35:03.505515+00:00
-- url     : https://prove2.me/theorems/55b1a66e-fa62-4bb8-ac9e-7b28247f8a23
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_53681a32a309da977bbe4451
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Guarded circuit normalizer

Public facade for the fixed raw-circuit-to-guarded-record TM2, its total exact
correctness theorem, and its all-input polynomial runtime certificate.
-/


