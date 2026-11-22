-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch8
-- name    : Polychromatic418967fa_Branch8
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:07:42.765528+00:00
-- url     : https://prove2.me/theorems/05d504a8-7ffe-44b5-97d2-b3345090a75e
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

def Polychromatic418967fa.branch_8 : allB 8 8 :=
allB_succ' 2 7 8 (Eq.refl Bool.true) (allA_of_3_0 2 7 8 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3 6 8 (Eq.refl Bool.true) (allA_succ_of_gcd 2 6 8 2 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 8 (accept_3_2 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 8))) (allB_succ' 4 5 8 (Eq.refl Bool.true) (allA_succ_of_accept 3 5 8 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 8 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 8 (accept_3_2 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 8)))) (allB_succ 4 8 (allA_of_3_0 4 4 8 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 8 (allA_succ_of_accept 2 3 8 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 8 (accept_3_2 1 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 8))) (allB_succ 2 8 (allA_succ_of_accept 1 2 8 (accept_3_2 1 2 8 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 8)) (allB_two 8))))))


