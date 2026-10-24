-- Prove2me | Definitions.Def_PricingWithTips3DM_d54ce948545465ee61145c59
-- name    : PricingWithTips3DM_d54ce948545465ee61145c59
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:47:59.531215+00:00
-- url     : https://prove2.me/theorems/13583878-1313-413e-9a88-887099fe9259
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauConstraints.Families
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_56366117e4d1003d36b71f79
import Definitions.Def_PricingWithTips3DM_c420edc6f78a19f1637236d3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cook--Levin whole-tableau constraint families

Stable facade for the proof-carrying serial validity and adjacent-transition
families.  Input shape, boundary constraints, and the final conjunction remain
separate circuitization layers.
-/


