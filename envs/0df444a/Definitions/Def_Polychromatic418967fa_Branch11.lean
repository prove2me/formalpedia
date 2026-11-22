-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch11
-- name    : Polychromatic418967fa_Branch11
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:07:34.166391+00:00
-- url     : https://prove2.me/theorems/4cfd71dd-f67e-443c-8e36-47a2fb26e6cf
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

def Polychromatic418967fa.branch_11 : allB 11 11 :=
allB_succ' 2 10 11 (Eq.refl Bool.true) (allA_of_3_0 2 10 11 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3 9 11 (Eq.refl Bool.true) (allA_succ_of_accept 2 9 11 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 11 (accept_3_2 1 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 11))) (allB_succ' 4 8 11 (Eq.refl Bool.true) (allA_succ_of_accept 3 8 11 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 11 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 11 (accept_3_2 1 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 11)))) (allB_succ' 5 7 11 (Eq.refl Bool.true) (allA_of_3_0 5 7 11 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 11 (allA_succ_of_accept 5 6 11 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 11 (accept_3_2 4 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 11 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 11 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 11 (accept_3_2 1 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 11)))))) (allB_succ 5 11 (allA_succ_of_accept 4 5 11 (accept_3_2 4 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 11 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 11 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 11 (accept_3_2 1 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 11))))) (allB_succ 4 11 (allA_of_3_0 4 4 11 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 11 (allA_succ_of_accept 2 3 11 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 11 (accept_3_2 1 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 11))) (allB_succ 2 11 (allA_succ_of_accept 1 2 11 (accept_3_2 1 2 11 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 11)) (allB_two 11)))))))))


