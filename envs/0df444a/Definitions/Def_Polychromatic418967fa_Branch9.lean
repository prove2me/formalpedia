-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch9
-- name    : Polychromatic418967fa_Branch9
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:07:28.607115+00:00
-- url     : https://prove2.me/theorems/cb2a426e-1bb9-4b2c-b14a-eb2ba14a5301
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

def Polychromatic418967fa.branch_9 : allB 9 9 :=
allB_succ' 2 8 9 (Eq.refl Bool.true) (allA_succ_of_accept 1 8 9 (accept_3_4 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 9)) (allB_succ' 3 7 9 (Eq.refl Bool.true) (allA_succ_of_accept 2 7 9 (accept_3_5 2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 7 9 (Polychromatic418967fa.accept_15_1_7_9_1_20 1 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 9))) (allB_succ' 4 6 9 (Eq.refl Bool.true) (allA_succ_of_gcd 3 6 9 3 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 9 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 9 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 9)))) (allB_succ 5 9 (allA_succ_of_accept 4 5 9 (accept_3_4 4 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 9 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 9 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 9 (accept_3_4 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 9))))) (allB_succ 4 9 (allA_succ_of_accept 3 4 9 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 4 9 (accept_3_5 2 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 9 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 4 9)))) (allB_succ 3 9 (allA_succ_of_accept 2 3 9 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 9 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 9))) (allB_succ 2 9 (allA_succ_of_accept 1 2 9 (accept_3_4 1 2 9 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 9)) (allB_two 9)))))))


