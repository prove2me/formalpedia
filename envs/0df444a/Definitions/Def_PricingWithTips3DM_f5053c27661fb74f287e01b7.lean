-- Prove2me | Definitions.Def_PricingWithTips3DM_f5053c27661fb74f287e01b7
-- name    : PricingWithTips3DM_f5053c27661fb74f287e01b7
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:10:51.986956+00:00
-- url     : https://prove2.me/theorems/422eb300-a607-4c49-923e-f79ac964bd59
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.OccurrenceRows
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_adcbf99c0fa60800ad77bb94
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Fixed-machine indexed occurrence rows

This facade exposes the semantic row theorem and the polynomial-time raw-input
machine while keeping controller simulation, termination, and arithmetic
bounds in smaller implementation files.
-/


