-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch7
-- name    : Polychromatic418967fa_Branch7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:06:55.220038+00:00
-- url     : https://prove2.me/theorems/aab8e392-d22f-495a-95c7-32fa349fd247
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

def Polychromatic418967fa.branch_7 : allB 7 7 :=
allB_succ' 2 6 7 (Eq.refl Bool.true) (allA_succ_of_accept 1 6 7 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 7)) (allB_succ' 3 5 7 (Eq.refl Bool.true) (allA_of_3_1 3 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 4 7 (allA_succ_of_accept 3 4 7 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 4 7 (accept_3_3 2 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 7 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 4 7)))) (allB_succ 3 7 (allA_succ_of_accept 2 3 7 (accept_3_3 2 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 7 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 7))) (allB_succ 2 7 (allA_of_3_1 2 2 7 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_two 7)))))


