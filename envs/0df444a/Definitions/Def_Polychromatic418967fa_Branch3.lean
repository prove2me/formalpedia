-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch3
-- name    : Polychromatic418967fa_Branch3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:07:39.84818+00:00
-- url     : https://prove2.me/theorems/f16e30d4-df8a-417e-8379-323b8edc300f
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_3 : allB 3 3 :=
allB_succ 2 3 (allA_succ_of_accept 1 2 3 (accept_3_4 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 3)) (allB_two 3)


