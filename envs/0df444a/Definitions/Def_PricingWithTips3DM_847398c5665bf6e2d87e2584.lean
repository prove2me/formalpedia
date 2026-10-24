-- Prove2me | Definitions.Def_PricingWithTips3DM_847398c5665bf6e2d87e2584
-- name    : PricingWithTips3DM_847398c5665bf6e2d87e2584
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:47:44.287993+00:00
-- url     : https://prove2.me/theorems/2d3a95ec-c6e4-4751-b6e8-835cdfc39af5
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.NonedgeFilter.Selector
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_01a9b2cbf2ae707d50ac89a5
import Definitions.Def_PricingWithTips3DM_559bc85b391ed65ee6a0a876
import Definitions.Def_PricingWithTips3DM_048074518e2d97cbf6f67793
import Definitions.Def_PricingWithTips3DM_d15c8b07cc17e00da1953b67
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Nonedge selector facade

Collects the small proof modules for the fixed candidate/answer selector.
-/


