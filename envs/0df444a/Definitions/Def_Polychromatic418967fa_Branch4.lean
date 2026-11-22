-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch4
-- name    : Polychromatic418967fa_Branch4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:07:42.471168+00:00
-- url     : https://prove2.me/theorems/59d6a2e1-7f8d-4122-a07e-0d50b3691395
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

def Polychromatic418967fa.branch_4 : allB 4 4 :=
allB_succ' 2 3 4 (Eq.refl Bool.true) (allA_succ_of_accept 1 3 4 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 4)) (allB_succ 2 4 (allA_of_3_1 2 2 4 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_two 4))


