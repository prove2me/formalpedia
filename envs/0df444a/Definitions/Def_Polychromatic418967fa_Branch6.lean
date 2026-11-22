-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch6
-- name    : Polychromatic418967fa_Branch6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:07:17.619192+00:00
-- url     : https://prove2.me/theorems/11991694-01ab-4cc6-9cc9-bff2ab2a2851
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

def Polychromatic418967fa.branch_6 : allB 6 6 :=
allB_succ' 2 5 6 (Eq.refl Bool.true) (allA_succ_of_accept 1 5 6 (accept_3_4 1 5 6 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 6)) (allB_succ' 3 4 6 (Eq.refl Bool.true) (allA_succ_of_gcd 2 4 6 2 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 6 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 4 6))) (allB_succ 3 6 (allA_succ_of_accept 2 3 6 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 6 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 6))) (allB_succ 2 6 (allA_succ_of_accept 1 2 6 (accept_3_4 1 2 6 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 6)) (allB_two 6))))


