-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch66
-- name    : Polychromatic418967fa_Branch66
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:08:49.897207+00:00
-- url     : https://prove2.me/theorems/8023db37-014c-4a0e-abcf-12d2b2bccb9d
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

def Polychromatic418967fa.branch_66 : allB 66 66 :=
  allB_succ' 2 65 66 (Eq.refl Bool.true) (allA_succ_of_accept 1 65 66 (accept_3_4 1 65 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 66)) (allB_succ' 3 64 66 (Eq.refl Bool.true) (allA_succ_of_gcd 2 64 66 2 1 32 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 66
  (Polychromatic418967fa.accept_27_1_10_12_1_2166 1 64 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 66))) (allB_succ' 4 63 66 (Eq.refl Bool.true) (allA_succ_of_gcd 3 63 66 3 1 21 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 66
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 63 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 63 66)))) (allB_succ' 5 62 66 (Eq.refl Bool.true) (allA_succ_of_gcd 4 62 66 2 2 31 33
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 66
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 62 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 66 2 1 31 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 66 (accept_3_4 1 62 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62 66)))))
  (allB_succ' 6 61 66 (Eq.refl Bool.true) (allA_succ_of_accept 5 61 66 (accept_3_5 5 61 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 61 66 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 61 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 66 (accept_3_5 2 61 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 66 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 61
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 66)))))) (allB_succ' 7 60 66 (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 60 66 6 1 10 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 60 66 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 60 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 66 2 2 30 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 60 66 3 1 20 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 60 66 2 1 30 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 66 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 60
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 66))))))) (allB_succ' 8 59 66 (Eq.refl
  Bool.true) (allA_succ_of_accept 7 59 66 (accept_3_4 7 59 66 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 59 66 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 59 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 66 (accept_3_4 4 59 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 66 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 59 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 66
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 59 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 66 (accept_3_4 1 59 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 66))))))))
  (allB_succ' 9 58 66 (Eq.refl Bool.true) (allA_succ_of_gcd 8 58 66 2 4 29 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 58 66 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 58
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 66 2 3 29 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 66 (accept_3_5 5 58
  66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 66 2 2 29 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 58 66
  (Polychromatic418967fa.accept_10_3_8_6_1_326 3 58 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 58 66 2 1 29 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 58 66 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 58 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 58 66))))))))) (allB_succ' 10 57 66 (Eq.refl Bool.true) (allA_succ_of_gcd 9
  57 66 3 3 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8
  57 66 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 57 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 57 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 66 3 2 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 66 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 57
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 66
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 57 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 57 66 3 1 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 57 66 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 57 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 66 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 57 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 66)))))))))) (allB_succ' 11 56 66 (Eq.refl
  Bool.true) (allA_succ_of_gcd 10 56 66 2 5 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 56 66 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 56 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 66 2 4 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 66 (accept_3_4 7 56 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 56 66 2 3 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 56 66 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 56 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 66 2 2 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 66 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 56
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 66 2 1 28 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 66 (accept_3_4 1 56
  66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 66))))))))))) (allB_succ' 12 55 66 (Eq.refl Bool.true)
  (allA_succ_of_gcd 11 55 66 11 1 5 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 55 66 (Polychromatic418967fa.accept_17_10_4_15_1_2165 10 55 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 66 (accept_3_5 8 55 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 66 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 55 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 66
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 66 (accept_3_5 5 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55 66
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 66 (Polychromatic418967fa.accept_14_3_13_10_1_761 3 55 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 66 (accept_3_5 2 55 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 66)))))))))))) (allB_succ' 13 54 66 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 54 66 6 2 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 66 (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 54 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 66 2 5 27 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 54 66 3 3 18 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 54 66 2 4 27 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 66 (Polychromatic418967fa.accept_19_7_16_9_1_398 7 54 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 66 6 1 9 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 66
  (Polychromatic418967fa.accept_10_5_4_6_1_319 5 54 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 54 66 2 2 27 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 54 66 3 1 18 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 54 66 2 1 27 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 66 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 54 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 66))))))))))))) (allB_succ' 14 53 66 (Eq.refl Bool.true)
  (allA_succ_of_accept 13 53 66 (accept_3_4 13 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53
  66 (Polychromatic418967fa.accept_21_12_11_3_1_1052 12 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 66 (accept_3_4 10 53 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 66 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 53 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 66
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 66 (accept_3_4 7 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 66
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 66 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 53 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 66 (accept_3_4 4 53 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 66 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 53
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 66 (accept_3_4 1 53 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 66)))))))))))))) (allB_succ' 15 52 66 (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 52 66 2 7 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 52 66 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 52 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 66 2 6 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 66 (accept_3_5 11 52 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 52 66 2 5 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 52 66 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 52 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 66 2 4 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 66 (Polychromatic418967fa.accept_20_7_12_6_1_2164 7
  52 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 66 2 3 26 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 66 (accept_3_5 5 52
  66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 66 2 2 26 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52 66
  (Polychromatic418967fa.accept_12_3_4_6_1_434 3 52 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 52 66 2 1 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 52 66 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 52 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 52 66))))))))))))))) (allB_succ' 16 51 66 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 51 66 3 5 17 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 51 66 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 51 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 66 3 4 17 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 66
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 51 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 66 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 51 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 66 3 3 17 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 66 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 51 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 66
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 51 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 51 66 3 2 17 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 51 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 66 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 51 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 66 3 1 17 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 66
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 51 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 51 66)))))))))))))))) (allB_succ' 17 50 66 (Eq.refl Bool.true) (allA_succ_of_gcd 16 50
  66 2 8 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  50 66 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 50 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 50 66 2 7 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 50 66 (accept_3_4 13 50 66 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 50 66 2 6 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 50 66 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 50 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 66 2 5 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 66 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 50 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 66 2 4 25 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 66 (accept_3_4 7 50 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 66 2 3 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 50 66 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 50 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 66 2 2 25 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 66
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 50 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 66 2 1 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 66 (accept_3_4 1 50 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  66))))))))))))))))) (allB_succ' 18 49 66 (Eq.refl Bool.true) (allA_succ_of_accept 17 49 66 (accept_3_5 17 49 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 66 (Polychromatic418967fa.accept_9_7_4_3_1_204 16
  49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 66
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 66 (accept_3_5 14 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 49
  66 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 49 66 (Polychromatic418967fa.accept_16_12_1_2_1_2163 12 49 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 66 (accept_3_5 11 49 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 49 66 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 49 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 66 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9
  49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 66 (accept_3_5 8 49 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 66
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 66 (accept_3_5 5 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 66
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 4 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 66 (accept_3_5 2 49 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 66 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 49 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 66)))))))))))))))))) (allB_succ' 19 48 66 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 48 66 6 3 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 66 (Polychromatic418967fa.accept_14_3_6_10_1_752 17 48 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 66 2 8 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 48 66 3 5 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 48 66 2 7 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 66 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 48 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 66 6 2 8 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 66
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 48 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 48 66 2 5 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 48 66 3 3 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 48 66 2 4 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 66 (Polychromatic418967fa.accept_19_7_10_9_1_2162 7 48 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 66 6 1 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 66 (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 48 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 66 2 2 24 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 48 66 3 1 16 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 48 66 2 1 24 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 66
  (Polychromatic418967fa.accept_15_1_3_6_1_621 1 48 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 66))))))))))))))))))) (allB_succ' 20 47 66 (Eq.refl Bool.true) (allA_succ_of_accept 19 47 66 (accept_3_4
  19 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 66
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 47 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 66 (accept_3_4 16 47 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 47 66 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 47 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 66 (Polychromatic418967fa.accept_9_5_2_3_1_194 14
  47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 66 (accept_3_4 13 47 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 66 (Polychromatic418967fa.accept_13_12_8_1_1_825
  12 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 66
  (Polychromatic418967fa.accept_10_1_7_6_1_91 11 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 66 (accept_3_4 10 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47
  66 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 47 66 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 47 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 66 (accept_3_4 7 47 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 47 66 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 47 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 66 (accept_3_4 4 47 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 66 (Polychromatic418967fa.accept_10_3_7_6_1_659 3
  47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 66
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 66 (accept_3_4 1 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  66)))))))))))))))))))) (allB_succ' 21 46 66 (Eq.refl Bool.true) (allA_succ_of_gcd 20 46 66 2 10 23 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 66
  (Polychromatic418967fa.accept_13_6_7_1_1_335 19 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 66 2 9 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 66 (accept_3_5 17 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46 66
  2 8 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 46
  66 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 46 66 2 7 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 46 66 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 46 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 66 2 6 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 66 (accept_3_5 11 46 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 46 66 2 5 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 46 66 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 46 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 46 66 2 4 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 46 66 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 46
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 66 2 3 23 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 66 (accept_3_5 5 46
  66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 66 2 2 23 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 46 66
  (Polychromatic418967fa.accept_12_3_10_6_1_442 3 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 46 66 2 1 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 46 66 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 46 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 46 66))))))))))))))))))))) (allB_succ' 22 45 66 (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 45 66 3 7 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 66 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 45 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 66 3 6 15 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 66
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 17 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 66 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 45 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 66 3 5 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 66 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 45 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 66
  (Polychromatic418967fa.accept_14_13_3_10_1_2159 13 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 66 3 4 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 66 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 45 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 66 3 3 15 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 66
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 66 3 2 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 66 (Polychromatic418967fa.accept_13_5_6_1_1_822 5 45 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 66
  (Polychromatic418967fa.accept_10_4_5_6_1_651 4 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 66 3 1 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 66 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 45 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 66 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 45 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 66)))))))))))))))))))))) (allB_succ' 23 44
  66 (Eq.refl Bool.true) (allA_succ_of_gcd 22 44 66 22 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 44 66 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 44 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 66 2 10 22 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 66 (accept_3_4 19 44 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 66 2 9 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 44 66 (Polychromatic418967fa.accept_13_4_5_1_1_833 17 44 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 66 2 8 22 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 66
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 44 66 2 7 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 44 66 (accept_3_4 13 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 66
  2 6 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 44 66
  11 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 44 66 2
  5 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 66
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 66 2 4 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 66 (accept_3_4 7 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 66 2
  3 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44 66
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 44 66 2 2 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 44 66 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 44 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 66 2 1 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 66 (accept_3_4 1 44 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 66))))))))))))))))))))))) (allB_succ' 24 43 66 (Eq.refl Bool.true) (allA_succ_of_accept 23 43
  66 (accept_3_5 23 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 66
  (Polychromatic418967fa.accept_9_4_7_3_1_43 22 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 43 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 66 (accept_3_5 20 43 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 43 66 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 43 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 66 (Polychromatic418967fa.accept_7_4_1_3_1_277 18
  43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 66 (accept_3_5 17 43 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 66 (Polychromatic418967fa.accept_7_2_1_3_1_102 16
  43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 66
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 66 (accept_3_5 14 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43
  66 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 43 66 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 43 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 66 (accept_3_5 11 43 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 43 66 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 43 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 66 (accept_3_5 8 43 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 66 (Polychromatic418967fa.accept_10_7_3_6_1_644 7
  43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 66
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 66 (accept_3_5 5 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 66
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 66 (Polychromatic418967fa.accept_13_3_4_1_1_363 3 43 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 66 (accept_3_5 2 43 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 66)))))))))))))))))))))))) (allB_succ' 25 42 66 (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 42 66 6 4 7 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 66 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 42 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 66 2 11 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 66 3 7 14 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 66 2 10 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 66 (Polychromatic418967fa.accept_9_1_6_3_1_177 19
  42 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 66 6 3 7 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 66
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 42 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 66 2 8 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 42 66 3 5 14 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 42 66 2 7 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 66 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 42 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 66 6 2 7 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 66 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 42 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 66 2 5 21 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 42 66 3 3 14 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 42 66 2 4 21 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 66
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 42 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 66 6 1 7 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 66 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 42 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 66 2 2 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 42 66 3 1 14 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 42 66 2 1 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 66 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 42 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 66))))))))))))))))))))))))) (allB_succ' 26
  41 66 (Eq.refl Bool.true) (allA_succ_of_accept 25 41 66 (accept_3_4 25 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 41 66 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 41 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 66 (accept_3_4 22 41 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 66
  (Polychromatic418967fa.accept_23_21_18_20_1_2158 21 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 66 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 41 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 66 (accept_3_4 19 41 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 66 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 41 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 66 (Polychromatic418967fa.accept_9_8_5_3_1_777 17
  41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 66 (accept_3_4 16 41 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 66
  (Polychromatic418967fa.accept_19_14_3_9_1_2157 14 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 66 (accept_3_4 13 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41
  66 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 41 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 66 (accept_3_4 10 41 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 41 66 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 41 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 66 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 41
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 66 (accept_3_4 7 41 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 66 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 41
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 66
  (Polychromatic418967fa.accept_10_5_1_6_1_672 5 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 66 (accept_3_4 4 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 66
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 66 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 41 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 66 (accept_3_4 1 41 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 66)))))))))))))))))))))))))) (allB_succ' 27 40 66 (Eq.refl Bool.true) (allA_succ_of_gcd 26 40
  66 2 13 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25
  40 66 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 40 66 2 12 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 40 66 (accept_3_5 23 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 40 66 2 11 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 40 66 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 40 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 66 2 10 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 66 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 40 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 66 2 9 20 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 66 (accept_3_5 17 40 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 66 2 8 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 40 66 (Polychromatic418967fa.accept_7_1_5_3_1_268 15
  40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 66 2 7 20 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 66
  (Polychromatic418967fa.accept_31_13_9_4_1_2156 13 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 40 66 2 6 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 40 66 (accept_3_5 11 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 66
  2 5 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 66
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 66 2 4 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 66 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 40 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 66 2 3 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 66 (accept_3_5 5 40 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 40 66 2 2 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 40 66 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 40 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 66 2 1 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 66 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 40
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40 66))))))))))))))))))))))))))) (allB_succ'
  28 39 66 (Eq.refl Bool.true) (allA_succ_of_gcd 27 39 66 3 9 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 66 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 39 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 66
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 66 3 8 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 66 (Polychromatic418967fa.accept_10_3_9_6_1_94 23 39 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 66 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 39 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 66 3 7 13 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 66
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 66 (Polychromatic418967fa.accept_15_4_9_6_1_627 19 39 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 66 3 6 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 66
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 66 3 5 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 66 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 39 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 66 3 4 13 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 66
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 66 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 39 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 66 3 3 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 66 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 39 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 66
  (Polychromatic418967fa.accept_14_7_11_10_1_2155 7 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 66 3 2 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 66 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 39 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 66 3 1 13 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 66
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 39 66)))))))))))))))))))))))))))) (allB_succ' 29 38 66 (Eq.refl Bool.true)
  (allA_succ_of_gcd 28 38 66 2 14 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 66 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 38 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 66 2 13 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 66 (accept_3_4 25 38 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 38 66 2 12 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 38 66 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 38 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 66 2 11 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 66 (Polychromatic418967fa.accept_12_9_2_6_1_455 21
  38 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 38 66 2 10 19 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 38 66 (accept_3_4 19 38
  66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38 66 2 9 19 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 38 66
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 38 66 2 8 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 38 66 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 38 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 66 2 7 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 66 (accept_3_4 13 38 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 38 66 2 6 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 38 66 (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 38 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 66 2 5 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 66 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 38
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 66 2 4 19 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 66 (accept_3_4 7 38
  66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 66 2 3 19 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38 66
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 66 2 2 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 66 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 38 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 66 2 1 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 66 (accept_3_4 1 38 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 66))))))))))))))))))))))))))))) (allB_succ' 30 37 66 (Eq.refl Bool.true) (allA_succ_of_accept
  29 37 66 (accept_3_5 29 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 66
  (Polychromatic418967fa.accept_15_13_7_6_1_682 28 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 37 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 66 (accept_3_5 26 37 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 37 66 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 37 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 66 (Polychromatic418967fa.accept_9_6_1_3_1_191 24
  37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 66 (accept_3_5 23 37 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 66 (Polychromatic418967fa.accept_7_1_2_3_1_257 22
  37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 66
  (Polychromatic418967fa.accept_10_1_7_6_1_91 21 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 66 (accept_3_5 20 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37
  66 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 66 (Polychromatic418967fa.accept_17_1_3_15_1_2153 18 37 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 66 (accept_3_5 17 37 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 66 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 37 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 66 (accept_3_5 14 37 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 66 (Polychromatic418967fa.accept_7_6_2_3_1_107 13
  37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 66
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 66 (accept_3_5 11 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37
  66 (Polychromatic418967fa.accept_13_10_11_1_1_2152 10 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 66 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 37 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 66 (accept_3_5 8 37 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 37 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 66 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 37
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 66 (accept_3_5 5 37 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 66 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 37
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 66
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 66 (accept_3_5 2 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 66
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 37 66)))))))))))))))))))))))))))))) (allB_succ' 31 36 66 (Eq.refl Bool.true) (allA_succ_of_gcd 30 36 66 6 5
  6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 66
  (Polychromatic418967fa.accept_21_8_15_3_1_279 29 36 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 36 66 2 14 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 36 66 3 9 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 36 66 2 13 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 66 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 36 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 66 6 4 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 66 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 36 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 66 2 11 18 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 36 66 3 7 12 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 36 66 2 10 18 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 66
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 36 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 66 6 3 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 66 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 36 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 66 2 8 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 36 66 3 5 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 36 66 2 7 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 66 (Polychromatic418967fa.accept_17_13_2_15_1_2151 13 36 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 66 6 2 6 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 66
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 36 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 36 66 2 5 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 36 66 3 3 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 36 66 2 4 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 66 (Polychromatic418967fa.accept_17_7_2_15_1_1255 7 36 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 66 6 1 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 66 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 36 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 66 2 2 18 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 36 66 3 1 12 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 36 66 2 1 18 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 66
  (Polychromatic418967fa.accept_19_1_17_9_1_2150 1 36 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 66))))))))))))))))))))))))))))))) (allB_succ' 32 35 66 (Eq.refl Bool.true) (allA_succ_of_accept 31 35 66
  (accept_3_4 31 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 66
  (Polychromatic418967fa.accept_20_10_15_6_1_2149 30 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 35 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 66 (accept_3_4 28 35 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 35 66 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 35 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 66 (Polychromatic418967fa.accept_15_11_5_6_1_669
  26 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 66 (accept_3_4 25 35
  66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 66 (Polychromatic418967fa.accept_9_6_8_3_1_183
  24 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 66
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 66 (accept_3_4 22 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35
  66 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 35 66 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 35 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 66 (accept_3_4 19 35 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 35 66 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 35 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 66 (accept_3_4 16 35 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 66 (Polychromatic418967fa.accept_9_6_8_3_1_183 15
  35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 66
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 66 (accept_3_4 13 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35
  66 (Polychromatic418967fa.accept_15_12_5_6_1_2148 12 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 66 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 35 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 66 (accept_3_4 10 35 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 66
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 8 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 66 (accept_3_4 7 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 66
  (Polychromatic418967fa.accept_9_6_8_3_1_183 6 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 66 (accept_3_4 4 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 35 66 (Polychromatic418967fa.accept_14_3_7_10_1_2146 3 35 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 66 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 35 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 66 (accept_3_4 1 35 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 35 66)))))))))))))))))))))))))))))))) (allB_succ' 33 34 66 (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 34 66 2 16 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 34 66 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 34 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 66 2 15 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 66 (accept_3_5 29 34 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 66 2 14 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 34 66 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 34 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 66 2 13 17 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 66
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 34 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 66 2 12 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 66 (accept_3_5 23 34 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 66
  2 11 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34
  66 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 34 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 34 66 2 10 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 34 66 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 34 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 66 2 9 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 66 (accept_3_5 17 34 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 34 66 2 8 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 34 66 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 34 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 66 2 7 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 66 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 34
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 66 2 6 17 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 66 (accept_3_5 11 34
  66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 66 2 5 17 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 66
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 34 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 66 2 4 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 66 (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 34 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 66 2 3 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 66 (accept_3_5 5 34 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 66 2 2 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 66 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 34 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 66 2 1 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 66 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 34
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 66)))))))))))))))))))))))))))))))))
  (allB_succ 33 66 (allA_succ_of_accept 32 33 66 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 33 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 33 66 3 10 11 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 66
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 66 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 33 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 66 3 9 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 66 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 33 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 66
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 33 66 3 8 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 33 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 33 66 11 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 33 66 3 7 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 66 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 33 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 66
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 33 66 3 6 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 33 66 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 33 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 66 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 33 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 66 3 5 11 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 66
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 66 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 33 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 66 3 4 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 33 66 11 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 33 66 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 33 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 66 3 3 11 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 66
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 66 3 2 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 66 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 33 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 66
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 66 3 1 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 66 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 33 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 66 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 33 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 66)))))))))))))))))))))))))))))))))
  (allB_succ 32 66 (allA_succ_of_accept 31 32 66 (accept_3_4 31 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 32 66 2 15 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 32 66 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 32 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 32 66 2 14 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 32 66 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 32 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 66 2 13 16 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 66 (accept_3_4 25 32 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 66 2 12 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 66 (Polychromatic418967fa.accept_15_8_2_6_1_2125 23
  32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 66 2 11 16 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 66
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 66 2 10 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 66 (accept_3_4 19 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 66
  2 9 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 32
  66 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 32 66 2 8 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 32 66 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 32 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 66 2 7 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 66 (accept_3_4 13 32 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 32 66 2 6 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 32 66 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 32 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 66 2 5 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 66 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 32
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 66 2 4 16 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 66 (accept_3_4 7 32
  66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 66 2 3 16 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32 66
  (Polychromatic418967fa.accept_13_5_6_1_1_822 5 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 66 2 2 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 66 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 32 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 66 2 1 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 66 (accept_3_4 1 32 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 66)))))))))))))))))))))))))))))))) (allB_succ 31 66 (allA_succ_of_accept 30 31 66
  (Polychromatic418967fa.accept_13_4_5_1_1_833 30 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 66 (accept_3_5 29 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 31
  66 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 31 66 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 31 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 66 (accept_3_5 26 31 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 31 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 66 (Polychromatic418967fa.accept_9_6_4_3_1_203 24
  31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 66 (accept_3_5 23 31 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 66 (Polychromatic418967fa.accept_10_2_1_6_1_634 22
  31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 66
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 66 (accept_3_5 20 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31
  66 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 66 (Polychromatic418967fa.accept_15_3_1_6_1_206 18 31 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 66 (accept_3_5 17 31 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 66 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 31 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 66 (Polychromatic418967fa.accept_9_6_4_3_1_203 15
  31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 66 (accept_3_5 14 31 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 66
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 66 (accept_3_5 11 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 31
  66 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 31 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 66 (accept_3_5 8 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 31 66 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 31 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 66 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 31 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 66 (accept_3_5 5 31 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 66 (Polychromatic418967fa.accept_13_4_5_1_1_833 4 31 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 66
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 31 66 (accept_3_5 2 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 66
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 31 66))))))))))))))))))))))))))))))) (allB_succ 30 66 (allA_succ_of_accept 29 30 66
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 30 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 66 2 14 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 30 66 3 9 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 30 66 2 13 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 30 66 (Polychromatic418967fa.accept_17_8_13_15_1_2143 25 30 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 66 6 4 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 66 (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 30 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 66 2 11 15 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 30 66 3 7 10 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 30 66 2 10 15 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 66
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 30 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 66 6 3 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 66 (Polychromatic418967fa.accept_19_17_11_9_1_2141 17 30 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 66 2 8 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 66 3 5 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 66 2 7 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 66 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 30 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 66 6 2 5 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 66
  (Polychromatic418967fa.accept_17_11_13_15_1_2140 11 30 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 66 2 5 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 30 66 3 3 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 30 66 2 4 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 66 (Polychromatic418967fa.accept_19_7_11_9_1_2139 7 30 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 66 6 1 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 66 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 30 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 66 2 2 15 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 30 66 3 1 10 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 30 66 2 1 15 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 66
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 30 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 30 66)))))))))))))))))))))))))))))) (allB_succ 29 66 (allA_succ_of_accept 28 29 66 (accept_3_4 28 29 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 66
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 66 (accept_3_4 25 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29
  66 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 29 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 29 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 66 (accept_3_4 22 29 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 29 66 (Polychromatic418967fa.accept_16_5_13_2_1_2138 21 29 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 66 (Polychromatic418967fa.accept_13_7_3_1_1_814 20
  29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 66 (accept_3_4 19 29 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 66 (Polychromatic418967fa.accept_7_4_1_3_1_277 18
  29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 66
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 66 (accept_3_4 16 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29
  66 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 66 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 29 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 66 (accept_3_4 13 29 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 66 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 29 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 66 (accept_3_4 10 29 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 66 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 29
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 66
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 66 (accept_3_4 7 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 66
  (Polychromatic418967fa.accept_9_6_2_3_1_771 6 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 66 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 29 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 66 (accept_3_4 4 29 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 66 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 29
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 66 (accept_3_4 1 29 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 66))))))))))))))))))))))))))))) (allB_succ 28 66
  (allA_succ_of_accept 27 28 66 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 28 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 66 2 13 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 66 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 28 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 66 2 12 14 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 66 (accept_3_5 23 28 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 66 2 11 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 66 (Polychromatic418967fa.accept_12_9_4_6_1_460 21
  28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 66 2 10 14 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 66
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 19 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 66 2 9 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 66 (accept_3_5 17 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28 66
  2 8 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 28
  66 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 28 66 2 7 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 28 66 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 28 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 66 2 6 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 66 (accept_3_5 11 28 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 28 66 2 5 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 28 66 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 28 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 66 2 4 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 66 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 28
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 66 2 3 14 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 66 (accept_3_5 5 28
  66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 66 2 2 14 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 66
  (Polychromatic418967fa.accept_10_3_8_6_1_326 3 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 66 2 1 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 66 (Polychromatic418967fa.accept_16_1_12_2_1_2136 1 28 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 66)))))))))))))))))))))))))))) (allB_succ 27 66 (allA_succ_of_accept 26
  27 66 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 27 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 66 3 8 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 66 (Polychromatic418967fa.accept_7_2_6_3_1_100 23
  27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 66
  (Polychromatic418967fa.accept_12_10_3_6_1_882 22 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 66 3 7 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 66 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 27 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 66 (Polychromatic418967fa.accept_17_2_10_15_1_1238 19 27 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 66 3 6 9 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 66
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 66 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 27 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 66 3 5 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 66 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 27 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 66
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 66 3 4 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 66 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 27 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 66 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 27 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 66 3 3 9 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 66
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 66 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 27 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 66 3 2 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 66
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 66 3 1 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 66 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 27 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 66))))))))))))))))))))))))))) (allB_succ 26
  66 (allA_succ_of_accept 25 26 66 (accept_3_4 25 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  66 2 12 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 66 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 26 66 2 11 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 26 66 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 26 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 66 2 10 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 66 (accept_3_4 19 26 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 26 66 2 9 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 26 66 (Polychromatic418967fa.accept_15_2_11_6_1_2135 17 26 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 66 2 8 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 66 (Polychromatic418967fa.accept_7_1_5_3_1_268 15
  26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 66 2 7 13 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 26 66 (accept_3_4 13 26
  66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 66 2 6 13 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26 66
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 26 66 2 5 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 26 66 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 26 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 66 2 4 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 66 (accept_3_4 7 26 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 26 66 2 3 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 26 66 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 26 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 66 2 2 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 66 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 26
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 66 2 1 13 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 66 (accept_3_4 1 26
  66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 66)))))))))))))))))))))))))) (allB_succ 25 66
  (allA_succ_of_accept 24 25 66 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 25 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 66 (accept_3_5 23 25 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 66 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 25 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 66 (Polychromatic418967fa.accept_10_1_5_6_1_649 21
  25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 66 (accept_3_5 20 25 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 66
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 66 (accept_3_5 17 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25
  66 (Polychromatic418967fa.accept_15_1_10_6_1_631 16 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 25 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 25 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 66 (accept_3_5 14 25 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 25 66 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 25 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 66 (Polychromatic418967fa.accept_15_12_10_6_1_2134
  12 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 66 (accept_3_5 11 25
  66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 66 (Polychromatic418967fa.accept_9_1_7_3_1_41
  10 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 66
  (Polychromatic418967fa.accept_10_9_5_6_1_691 9 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 66 (accept_3_5 8 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 66
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 25 66 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 25 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 66 (accept_3_5 5 25 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 25 66 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 25 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 66 (accept_3_5 2 25 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 66 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 25
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 66))))))))))))))))))))))))) (allB_succ 24
  66 (allA_succ_of_accept 23 24 66 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 24 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 66 2 11 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 24 66 3 7 8 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 24 66 2 10 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 66 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 24 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 66 6 3 4 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 66
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 24 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 24 66 2 8 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 24 66 3 5 8 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 24 66 2 7 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 66 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 24 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 66 6 2 4 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 66 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 24 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 66 2 5 12 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 66 3 3 8 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 66 2 4 12 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 66
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 24 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 66 6 1 4 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 66 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 24 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 66 2 2 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 24 66 3 1 8 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 24 66 2 1 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 66 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 24 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 66)))))))))))))))))))))))) (allB_succ 23 66
  (allA_succ_of_accept 22 23 66 (accept_3_4 22 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23
  66 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 66 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 23 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 66 (accept_3_4 19 23 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 66 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 23 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 66 (accept_3_4 16 23 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 66 (Polychromatic418967fa.accept_7_1_2_3_1_257 15
  23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 66
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 14 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 66 (accept_3_4 13 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23
  66 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 23 66 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 23 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 66 (accept_3_4 10 23 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 23 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 66 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 23
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 66 (accept_3_4 7 23 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 66 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 23
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 66
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 66 (accept_3_4 4 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 66
  (Polychromatic418967fa.accept_25_3_23_16_1_2132 3 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 66 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 23 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 66 (accept_3_4 1 23 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 66))))))))))))))))))))))) (allB_succ 22 66 (allA_succ_of_accept 21 22 66
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 22 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 66 2 10 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 66 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 22 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 66 2 9 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 66 (accept_3_5 17 22 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 66 2 8 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 66 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 22 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 66 2 7 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 66 (Polychromatic418967fa.accept_15_13_7_6_1_682 13
  22 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 66 2 6 11 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 22 66 11 1 2 6 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 22 66 2 5 11 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 66
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 22 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 66 2 4 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 66 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 22 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 66 2 3 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 66 (accept_3_5 5 22 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 66 2 2 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 66 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 22 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 66 2 1 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 66 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 22
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 66)))))))))))))))))))))) (allB_succ 21 66
  (allA_succ_of_accept 20 21 66 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 21 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 66 3 6 7 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 66
  (Polychromatic418967fa.accept_10_7_1_6_1_673 17 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 66 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 21 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 66 3 5 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 66 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 21 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 66
  (Polychromatic418967fa.accept_16_13_5_2_1_2131 13 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 66 3 4 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 66 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 21 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 66 3 3 7 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 66
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 66 3 2 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 66 (Polychromatic418967fa.accept_10_5_1_6_1_672 5 21 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 66
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 66 3 1 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 66 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 21 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 66 (Polychromatic418967fa.accept_18_1_3_12_1_467 1 21 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 66))))))))))))))))))))) (allB_succ 20 66
  (allA_succ_of_accept 19 20 66 (accept_3_4 19 20 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 66
  2 9 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20
  66 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 20 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 66 2 8 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 66 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 20 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 66 2 7 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 66 (accept_3_4 13 20 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 66 2 6 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 66 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 20 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 66 2 5 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 66 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 20
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 66 2 4 10 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 66 (accept_3_4 7 20
  66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 66 2 3 10 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20 66
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 20 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 66 2 2 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 66 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 20 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 66 2 1 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 66 (accept_3_4 1 20 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 66)))))))))))))))))))) (allB_succ 19 66 (allA_succ_of_accept 18 19 66
  (Polychromatic418967fa.accept_13_5_6_1_1_822 18 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 66 (accept_3_5 17 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19
  66 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 19 66 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 19 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 66 (accept_3_5 14 19 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 19 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 66 (Polychromatic418967fa.accept_14_12_5_10_1_2130
  12 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 66 (accept_3_5 11 19
  66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 66
  (Polychromatic418967fa.accept_15_10_4_6_1_2129 10 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 19 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 66 (accept_3_5 8 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 19 66 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 19 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 66 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 19 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 66 (accept_3_5 5 19 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 66 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 19 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 66
  (Polychromatic418967fa.accept_10_3_9_6_1_94 3 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 19 66 (accept_3_5 2 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 66
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 19 66))))))))))))))))))) (allB_succ 18 66 (allA_succ_of_accept 17 18 66
  (Polychromatic418967fa.accept_13_4_5_1_1_833 17 18 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 18 66 2 8 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 18 66 3 5 6 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 18 66 2 7 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 66 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 18 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 66 6 2 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 66 (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 18 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 66 2 5 9 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 18 66 3 3 6 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 18 66 2 4 9 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 66
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 7 18 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 66 6 1 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 66 (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 18 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 66 2 2 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 66 3 1 6 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 66 2 1 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 66 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 18 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 66)))))))))))))))))) (allB_succ 17 66
  (allA_succ_of_accept 16 17 66 (accept_3_4 16 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17
  66 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 66 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 17 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 66 (accept_3_4 13 17 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 66 (Polychromatic418967fa.accept_15_12_2_6_1_2127 12 17 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 66 (accept_3_4 10 17 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 66 (Polychromatic418967fa.accept_16_9_1_2_1_2126 9
  17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 66
  (Polychromatic418967fa.accept_15_8_2_6_1_2125 8 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 66 (accept_3_4 7 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 66
  (Polychromatic418967fa.accept_9_6_8_3_1_183 6 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 66 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 17 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 66 (accept_3_4 4 17 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 66 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 17
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 66 (accept_3_4 1 17 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 66))))))))))))))))) (allB_succ 16 66 (allA_succ_of_accept 15 16
  66 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 16 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 66 2 7 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 66 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 16 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 66 2 6 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 66 (accept_3_5 11 16 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 66 2 5 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 66 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 16 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 66 2 4 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 66 (Polychromatic418967fa.accept_13_7_3_1_1_814 7 16
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 66 2 3 8 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 66 (accept_3_5 5 16 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 66 2 2 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 66 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 16 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 16 66 2 1 8 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 16 66
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 16 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 66)))))))))))))))) (allB_succ 15 66 (allA_succ_of_accept 14 15 66
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 66 3 4 5 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 66 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 15 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 66
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 66 3 3 5 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 66 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 15 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 66 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 15 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 66 3 2 5 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 66
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 66 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 15 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 66 3 1 5 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 66 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 15 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 66
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 66))))))))))))))) (allB_succ 14 66 (allA_succ_of_accept 13 14 66 (accept_3_4 13 14 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 66 2 6 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 14 66 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 14 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 66 2 5 7 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 66
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 14 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 14 66 2 4 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 14 66 (accept_3_4 7 14 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 14 66 2
  3 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14 66
  (Polychromatic418967fa.accept_10_5_4_6_1_319 5 14 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 14 66 2 2 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 14 66 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 14 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 66 2 1 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 66 (accept_3_4 1 14 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 66)))))))))))))) (allB_succ 13 66 (allA_succ_of_accept 12 13 66
  (Polychromatic418967fa.accept_21_12_13_3_1_2124 12 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 66 (accept_3_5 11 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13
  66 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 13 66 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 13 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 66 (accept_3_5 8 13 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 13 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 66 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 13
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 66 (accept_3_5 5 13 66
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13 66 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 13
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 66
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 13 66 (accept_3_5 2 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 66
  (Polychromatic418967fa.accept_9_1_4_3_1_201 1 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 13 66))))))))))))) (allB_succ 12 66 (allA_succ_of_accept 11 12 66
  (Polychromatic418967fa.accept_10_1_2_6_1_638 11 12 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 66 2 5 6 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 12 66 3 3 4 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 12 66 2 4 6 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 66 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 12 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 66 6 1 2 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 66 (Polychromatic418967fa.accept_13_5_12_1_1_2123 5 12 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 66 2 2 6 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 12 66 3 1 4 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 12 66 2 1 6 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 66
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 12 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 66)))))))))))) (allB_succ 11 66 (allA_succ_of_accept 10 11 66 (accept_3_4 10 11 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 66
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 66 (accept_3_4 7 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11 66
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 66 (accept_3_4 4 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 11 66 (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 11 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 66 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 11 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 66 (accept_3_4 1 11 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 11 66))))))))))) (allB_succ 10 66 (allA_succ_of_accept 9 10 66
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 10 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 66 2 4 5 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 66 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 10 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 66 2 3 5 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 66 (accept_3_5 5 10 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 10 66 2 2 5 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 10 66 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 10 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 66 2 1 5 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 66 (Polychromatic418967fa.accept_15_1_10_6_1_631 1
  10 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 66)))))))))) (allB_succ 9 66
  (allA_succ_of_accept 8 9 66 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 9 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 66 3 2 3 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 66 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 9 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 66
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 9 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 66 3 1 3 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 66 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 9 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 66 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 9 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 66))))))))) (allB_succ 8 66
  (allA_succ_of_accept 7 8 66 (accept_3_4 7 8 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 66 2 3 4
  33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 66
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 8 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 8 66 2 2 4 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 8 66 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 8 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 66 2 1 4 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 66 (accept_3_4 1 8 66 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 8 66)))))))) (allB_succ 7 66 (allA_succ_of_accept 6 7 66 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 7 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 7 66 (accept_3_5 5 7 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 66 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 7 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 7 66
  (Polychromatic418967fa.accept_10_3_7_6_1_659 3 7 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 7 66 (accept_3_5 2 7 66 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 7 66
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 7 66))))))) (allB_succ 6 66 (allA_succ_of_accept 5 6 66 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 6 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 66 2 2 3 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 6 66 3 1 2 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 6 66 2 1 3 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 66
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 6 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 66)))))) (allB_succ 5 66 (allA_succ_of_accept 4 5 66 (accept_3_4 4 5 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 66 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 5 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 66 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 5 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 66 (accept_3_4 1 5 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 5 66))))) (allB_succ 4 66 (allA_succ_of_accept 3 4 66
  (Polychromatic418967fa.accept_12_3_4_6_1_434 3 4 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 4 66 2 1 2 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 4 66 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 4 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 4 66)))) (allB_succ 3 66 (allA_succ_of_accept 2 3 66
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 3 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 66 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 3 66))) (allB_succ 2 66 (allA_succ_of_accept 1 2 66 (accept_3_4 1 2 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 2 66)) (allB_two
  66))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


