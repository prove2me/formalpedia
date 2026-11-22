-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch10
-- name    : Polychromatic418967fa_Branch10
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:07:32.268566+00:00
-- url     : https://prove2.me/theorems/cf54af73-c808-419f-b4aa-a7b226ff75b7
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

def Polychromatic418967fa.branch_10 : allB 10 10 :=
allB_succ' 2 9 10 (Eq.refl Bool.true) (allA_succ_of_accept 1 9 10 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 10)) (allB_succ' 3 8 10 (Eq.refl Bool.true) (allA_of_3_1 3 8 10 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 7 10 (Eq.refl Bool.true) (allA_succ_of_accept 3 7 10 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 10 (accept_3_3 2 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 7 10 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 10)))) (allB_succ' 5 6 10 (Eq.refl Bool.true) (allA_succ_of_gcd 4 6 10 2 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 10 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 6 10 2 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 10 (Polychromatic418967fa.accept_15_1_6_10_1_23 1 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 10))))) (allB_succ 5 10 (allA_of_3_1 5 5 10 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 4 10 (allA_succ_of_accept 3 4 10 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 10 2 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 10 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 4 10)))) (allB_succ 3 10 (allA_succ_of_accept 2 3 10 (accept_3_3 2 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 10 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 10))) (allB_succ 2 10 (allA_of_3_1 2 2 10 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_two 10))))))))


