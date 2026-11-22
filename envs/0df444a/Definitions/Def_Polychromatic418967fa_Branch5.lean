-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch5
-- name    : Polychromatic418967fa_Branch5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:07:59.091496+00:00
-- url     : https://prove2.me/theorems/4c30b97b-9a55-4d7a-b76c-03460baa3b88
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

def Polychromatic418967fa.branch_5 : allB 5 5 :=
allB_succ' 2 4 5 (Eq.refl Bool.true) (allA_of_3_0 2 4 5 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 5 (allA_succ_of_accept 2 3 5 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 5 (accept_3_2 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 5))) (allB_succ 2 5 (allA_succ_of_accept 1 2 5 (accept_3_2 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 5)) (allB_two 5)))


