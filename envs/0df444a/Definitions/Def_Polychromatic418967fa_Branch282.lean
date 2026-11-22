-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch282
-- name    : Polychromatic418967fa_Branch282
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:33:08.62619+00:00
-- url     : https://prove2.me/theorems/01ea0a33-c3b8-42c9-a428-aaca5b3e3d20
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch282_Segment003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_282 : allB 282 282 :=
  allB_succ' 2 281 282 (Eq.refl Bool.true) (allA_succ_of_accept 1 281 282 (accept_3_4 1 281 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 281 282)) (allB_succ' 3 280 282 (Eq.refl Bool.true) (allA_succ_of_gcd 2 280 282 2 1 140
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 280 282
  (Polychromatic418967fa.accept_27_1_10_12_1_2166 1 280 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 280 282))) (allB_succ' 4 279 282 (Eq.refl Bool.true) (allA_succ_of_gcd 3 279 282 3 1 93 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 279 282
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 279 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 279 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 279 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 279 282)))) (allB_succ' 5 278 282 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  278 282 2 2 139 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 278 282 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 278 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 278 282 2 1 139 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 278 282 (accept_3_4 1 278 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 278 282))))) (allB_succ' 6 277 282 (Eq.refl Bool.true) (allA_succ_of_accept 5 277 282
  (accept_3_5 5 277 282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 277 282
  (Polychromatic418967fa.accept_9_4_7_3_1_43 4 277 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 277 282 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 277 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 277 282 (accept_3_5 2 277 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 277 282 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 277 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 277 282)))))) (allB_succ' 7 276 282 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 276 282 6 1 46 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 276 282 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 276 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 276 282 2 2 138 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 276 282 3 1 92 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 276 282 2 1 138 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 276 282
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 276 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 276 282))))))) (allB_succ' 8 275 282 (Eq.refl Bool.true) (allA_succ_of_accept 7 275 282 (accept_3_4 7 275
  282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 275 282
  (Polychromatic418967fa.accept_9_6_5_3_1_205 6 275 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 275 282 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 275 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 275 282 (accept_3_4 4 275 282 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 275 282 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 275 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 275 282 (Polychromatic418967fa.accept_9_2_5_3_1_37 2
  275 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 275 282 (accept_3_4 1 275
  282 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 275 282)))))))) (allB_succ' 9 274 282 (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 274 282 2 4 137 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 274 282 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 274 282 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 274 282 2 3 137 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 274 282 (accept_3_5 5 274 282 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 274 282 2 2 137 141 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 274 282 (Polychromatic418967fa.accept_7_3_1_2_1_247 3
  274 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 274 282 2 1 137 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 274 282
  (Polychromatic418967fa.accept_9_1_4_3_1_201 1 274 282 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 274 282))))))))) (Polychromatic418967fa.branch_282_segment_003))))))))


