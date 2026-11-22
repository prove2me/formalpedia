-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch105
-- name    : Polychromatic418967fa_Branch105
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:10:51.70791+00:00
-- url     : https://prove2.me/theorems/4844d384-c3d4-4aeb-98b5-81bf3e7d7b14
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

def Polychromatic418967fa.branch_105 : allB 105 105 :=
  allB_succ' 2 104 105 (Eq.refl Bool.true) (allA_succ_of_accept 1 104 105 (accept_3_4 1 104 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104 105)) (allB_succ' 3 103 105 (Eq.refl Bool.true) (allA_succ_of_accept 2 103 105
  (accept_3_5 2 103 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 105
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 103 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 103 105))) (allB_succ' 4 102 105 (Eq.refl Bool.true) (allA_succ_of_gcd 3 102 105 3 1 34 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 102 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 102 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 102 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 102 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 102 105)))) (allB_succ' 5 101 105 (Eq.refl Bool.true) (allA_succ_of_accept 4
  101 105 (accept_3_4 4 101 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 105
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 101 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 101 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 101 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 105 (accept_3_4 1 101 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 101 105))))) (allB_succ' 6 100 105 (Eq.refl Bool.true) (allA_succ_of_gcd 5 100 105 5 1 20 21
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 100 105
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 100 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 100 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 100 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 105 (accept_3_5 2 100 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 100 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 100 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 105)))))) (allB_succ' 7 99 105 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 99 105 3 2 33 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 99 105 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 99 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 105 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 99 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 105 3 1 33 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 105 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 99 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99 105))))))) (allB_succ' 8 98 105 (Eq.refl Bool.true) (allA_succ_of_gcd 7
  98 105 7 1 14 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  6 98 105 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 98 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 98 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 98 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 105 (accept_3_4 4 98 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 98 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 105
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 98 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 98 105 (accept_3_4 1 98 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98 105))))))))
  (allB_succ' 9 97 105 (Eq.refl Bool.true) (allA_succ_of_accept 8 97 105 (accept_3_5 8 97 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 105 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 97 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 105
  (Polychromatic418967fa.accept_14_6_13_7_1_2015 6 97 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 105 (accept_3_5 5 97 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  105 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 97 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 105 (accept_3_5 2 97 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 105 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 97 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 105))))))))) (allB_succ' 10 96 105 (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 96 105 3 3 32 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 96 105 (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 96 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 105 (Polychromatic418967fa.accept_19_7_1_10_1_4702 7 96 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 105 3 2 32 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 105
  (Polychromatic418967fa.accept_14_5_12_7_1_2767 5 96 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 105 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 96 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 96 105 3 1 32 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 96 105 (Polychromatic418967fa.accept_14_2_12_7_1_617 2 96 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 105
  (Polychromatic418967fa.accept_10_1_6_5_1_304 1 96 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 105)))))))))) (allB_succ' 11 95 105 (Eq.refl Bool.true) (allA_succ_of_gcd 10 95 105 5 2 19 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 95 105
  (Polychromatic418967fa.accept_17_9_10_3_1_3423 9 95 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 95 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 105 (accept_3_4 7 95 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 95 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 95 105 5 1 19 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 95 105 (accept_3_4 4 95 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 95 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 105 (accept_3_4 1 95 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  105))))))))))) (allB_succ' 12 94 105 (Eq.refl Bool.true) (allA_succ_of_accept 11 94 105 (accept_3_5 11 94 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 105 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 94 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 105
  (Polychromatic418967fa.accept_10_9_4_5_1_616 9 94 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 105 (accept_3_5 8 94 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  105 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 105 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 94 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 105 (accept_3_5 5 94 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 105 (Polychromatic418967fa.accept_13_4_3_1_1_2898 4 94 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 105 (accept_3_5 2 94 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 94
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 105)))))))))))) (allB_succ' 13 93 105
  (Eq.refl Bool.true) (allA_succ_of_gcd 12 93 105 3 4 31 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 93 105 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 93 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 105
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 93 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 93 105 3 3 31 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 93 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 93 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 105 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 93 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 105 3 2 31 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 105
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 93 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 105 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 93 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 105 3 1 31 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 105 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 93 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 105
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 93 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 93 105))))))))))))) (allB_succ' 14 92 105 (Eq.refl Bool.true) (allA_succ_of_accept 13 92 105 (accept_3_4 13
  92 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 92 105
  (Polychromatic418967fa.accept_9_3_2_6_1_264 12 92 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 92 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 105 (accept_3_4 10 92 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 92 105 (Polychromatic418967fa.accept_19_9_16_10_1_4701 9 92 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 105 (Polychromatic418967fa.accept_9_8_2_6_1_875 8
  92 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 92 105 (accept_3_4 7 92 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92 105 (Polychromatic418967fa.accept_12_6_8_9_1_553 6
  92 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 92 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 92 105 (accept_3_4 4 92 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 92
  105 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 92 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 92 105 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 92 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 105 (accept_3_4 1 92 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92 105)))))))))))))) (allB_succ' 15 91 105 (Eq.refl Bool.true) (allA_succ_of_gcd 14 91 105 7 2
  13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 91 105
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 91 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 91 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 91 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 105 (accept_3_5 11 91 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 91 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 105 (Polychromatic418967fa.accept_10_9_1_5_1_594 9
  91 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 105 (accept_3_5 8 91 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 91 105 7 1 13 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 91 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 105 (accept_3_5 5 91 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 105
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 91 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 105 (accept_3_5 2 91 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  105 (Polychromatic418967fa.accept_17_1_6_3_1_4700 1 91 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 91 105))))))))))))))) (allB_succ' 16 90 105 (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 105 15 1
  6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 105
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 90 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 105 (Polychromatic418967fa.accept_14_13_6_7_1_2013 13 90 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 105 3 4 30 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 105 5 2 18 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 90 105 3 3 30 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 90 105
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 90 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 90 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 105 3 2 30 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 90 105 5 1 18 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 90 105 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 90 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 105 3 1 30 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 105
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 90 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 105 (Polychromatic418967fa.accept_14_1_6_7_1_1936 1 90 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90 105)))))))))))))))) (allB_succ' 17 89 105 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 89 105 (accept_3_4 16 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 105 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 89 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 105 (accept_3_4 13 89 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 89 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 105
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 105 (accept_3_4 10 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 105 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 105 (accept_3_4 7 89 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 105 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 89 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 105
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 105 (accept_3_4 4 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  105 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 89 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 105 (accept_3_4 1 89 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 105))))))))))))))))) (allB_succ' 18 88 105 (Eq.refl Bool.true) (allA_succ_of_accept 17 88 105
  (accept_3_5 17 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 105
  (Polychromatic418967fa.accept_25_16_13_5_1_4699 16 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 88 105 (Polychromatic418967fa.accept_16_15_8_9_1_2563 15 88 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 105 (accept_3_5 14 88 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 88 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 12
  88 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 105 (accept_3_5 11 88
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 105 (Polychromatic418967fa.accept_9_1_7_6_1_75
  10 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 105
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 105 (accept_3_5 8 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  105 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 88 105 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 88 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 105 (accept_3_5 5 88 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 88 105 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 88 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 88
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 105 (accept_3_5 2 88 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88 105)))))))))))))))))) (allB_succ' 19 87
  105 (Eq.refl Bool.true) (allA_succ_of_gcd 18 87 105 3 6 29 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 105 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 87 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 105
  (Polychromatic418967fa.accept_11_5_10_6_1_793 16 87 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 105 3 5 29 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 105 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 87 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 105 3 4 29 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 105
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 87 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 105 3 3 29 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 105 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 87 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 105
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 87 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 105 3 2 29 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 105 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 87 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 105 (Polychromatic418967fa.accept_14_4_3_7_1_3702 4 87 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 105 3 1 29 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 105 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 87 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87 105))))))))))))))))))) (allB_succ' 20 86 105 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 86 105 (accept_3_4 19 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 105 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 86 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 105 (accept_3_4 16 86 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 105
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 105 (accept_3_4 13 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 105 (accept_3_4 10 86 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 105 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 86 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 105
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 105 (accept_3_4 7 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  105 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 86 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 105 (accept_3_4 4 86 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 105 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 105 (accept_3_4 1 86 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86 105)))))))))))))))))))) (allB_succ' 21 85 105 (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 85 105 5 4 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 85 105 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 85 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 105
  (Polychromatic418967fa.accept_19_18_9_10_1_4698 18 85 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 105 (accept_3_5 17 85 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 85 105 5 3 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 85 105 (accept_3_5 14 85 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 85 105 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 85 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 105 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 85 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 105 (accept_3_5 11 85 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 85 105 5 2 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 85 105 (Polychromatic418967fa.accept_23_9_16_13_1_4697
  9 85 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 105 (accept_3_5 8 85
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 105 (Polychromatic418967fa.accept_9_7_4_6_1_273
  7 85 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 105
  (Polychromatic418967fa.accept_13_6_7_1_1_335 6 85 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 85 105 5 1 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 85 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 105 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 85 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 105 (accept_3_5 2 85 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 105 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 85
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 105))))))))))))))))))))) (allB_succ' 22
  84 105 (Eq.refl Bool.true) (allA_succ_of_gcd 21 84 105 21 1 4 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 84 105 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 84 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 105
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 84 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 105 3 6 28 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 84 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 105 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 84 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 84 105 3 5 28 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 84 105 7 2 12 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 105
  (Polychromatic418967fa.accept_8_5_4_1_1_111 13 84 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 105 3 4 28 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 105 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 84 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 84 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 105 3 3 28 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 105
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 84 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 84 105 7 1 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 84 105 3 2 28 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 84 105 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 84 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 84 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 84 105 3 1 28 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 84 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 84 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 84 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 84 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84 105)))))))))))))))))))))) (allB_succ' 23 83 105 (Eq.refl Bool.true)
  (allA_succ_of_accept 22 83 105 (accept_3_4 22 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 105 (accept_3_4 19 83 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 105
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 105 (accept_3_4 16 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 105 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 105 (accept_3_4 13 83 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 83 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 105
  (Polychromatic418967fa.accept_25_11_8_5_1_4696 11 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 105 (accept_3_4 10 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 105 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 105 (accept_3_4 7 83 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 105
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 105 (accept_3_4 4 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  105 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 105 (accept_3_4 1 83 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 105))))))))))))))))))))))) (allB_succ' 24 82 105 (Eq.refl Bool.true) (allA_succ_of_accept 23
  82 105 (accept_3_5 23 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 105
  (Polychromatic418967fa.accept_9_4_1_6_1_284 22 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 82 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 82 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 105 (accept_3_5 20 82 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 82 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 105 (Polychromatic418967fa.accept_10_8_2_5_1_596
  18 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 105 (accept_3_5 17
  82 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 105
  (Polychromatic418967fa.accept_9_7_1_6_1_261 16 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 82 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 105 (accept_3_5 14 82 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 82 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 82 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 12
  82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 105 (accept_3_5 11 82
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 105
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 82 105 (Polychromatic418967fa.accept_14_9_12_7_1_597 9 82 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 105 (accept_3_5 8 82 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 82 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 105 (Polychromatic418967fa.accept_12_6_10_9_1_531 6
  82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 105 (accept_3_5 5 82 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82 105 (Polychromatic418967fa.accept_9_4_1_6_1_284 4
  82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 82 105 (accept_3_5 2 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82
  105 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 82 105)))))))))))))))))))))))) (allB_succ' 25 81 105 (Eq.refl Bool.true) (allA_succ_of_gcd 24 81 105 3 8 27
  35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 105
  (Polychromatic418967fa.accept_18_5_9_15_1_4695 23 81 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 105 (Polychromatic418967fa.accept_18_4_9_15_1_3383 22 81 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 105 3 7 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 105 (Polychromatic418967fa.accept_13_7_3_1_1_814 20 81 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 105
  (Polychromatic418967fa.accept_10_9_1_5_1_594 19 81 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 105 3 6 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 105 (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 81 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 105 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 81 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 105 3 5 27 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 105
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 81 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 105 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 81 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 105 3 4 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 105 (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 81 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 105
  (Polychromatic418967fa.accept_14_10_11_7_1_1955 10 81 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 105 3 3 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 105 (Polychromatic418967fa.accept_16_8_1_9_1_847 8 81 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 105 (Polychromatic418967fa.accept_13_7_3_1_1_814 7 81 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 105 3 2 27 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 105
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 81 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 105 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 81 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 105 3 1 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 105 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 81 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 105
  (Polychromatic418967fa.accept_23_1_12_13_1_4694 1 81 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 105))))))))))))))))))))))))) (allB_succ' 26 80 105 (Eq.refl Bool.true) (allA_succ_of_gcd 25 80 105 5 5 16
  21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 80 105
  (Polychromatic418967fa.accept_17_7_12_3_1_4693 24 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 80 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 105 (accept_3_4 22 80 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 80 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 80 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 105 5 4 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 105 (accept_3_4 19 80 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 80 105 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 80 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 80 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 80 105 (accept_3_4 16 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 80
  105 5 3 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  80 105 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 80 105 (accept_3_4 13 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 80 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 80 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 80 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 105 5 2 16 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 105
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 80 105 (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 80 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 105 (accept_3_4 7 80 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 80 105 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 80 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 80 105 5 1 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 80 105 (accept_3_4 4 80 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 80 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 105
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 80 105 (accept_3_4 1 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  105)))))))))))))))))))))))))) (allB_succ' 27 79 105 (Eq.refl Bool.true) (allA_succ_of_accept 26 79 105 (accept_3_5 26
  79 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 105
  (Polychromatic418967fa.accept_28_25_23_21_1_4692 25 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 105 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 79 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 105 (accept_3_5 23 79 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 105
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 105 (accept_3_5 20 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 105 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 105 (accept_3_5 17 79 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 105
  (Polychromatic418967fa.accept_11_4_2_6_1_389 15 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 105 (accept_3_5 14 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 105 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 79 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 105 (accept_3_5 11 79 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 105
  (Polychromatic418967fa.accept_17_9_11_3_1_2353 9 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 105 (accept_3_5 8 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  105 (Polychromatic418967fa.accept_19_7_3_10_1_4674 7 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 105 (accept_3_5 5 79 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 105
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 105 (accept_3_5 2 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  105 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 105))))))))))))))))))))))))))) (allB_succ' 28 78 105 (Eq.refl Bool.true) (allA_succ_of_gcd 27 78 105 3 9
  26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 78 105
  (Polychromatic418967fa.accept_12_2_6_9_1_19 26 78 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 78 105 (Polychromatic418967fa.accept_19_6_2_10_1_4691 25 78 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 105 3 8 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 105
  (Polychromatic418967fa.accept_10_2_8_5_1_587 22 78 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 78 105 3 7 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 78 105 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 78 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 105 3 6 26 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 105
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 78 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 105 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 78 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 78 105 3 5 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 78 105 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 78 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 105
  (Polychromatic418967fa.accept_10_3_8_5_1_606 13 78 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 105 3 4 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 105 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 78 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 105 3 3 26 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 105
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 78 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 78 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 105 3 2 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 105 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 78 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 105
  (Polychromatic418967fa.accept_12_4_6_9_1_548 4 78 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 78 105 3 1 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 78 105 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 78 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 105 (Polychromatic418967fa.accept_14_1_8_7_1_1253 1 78 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 105)))))))))))))))))))))))))))) (allB_succ'
  29 77 105 (Eq.refl Bool.true) (allA_succ_of_gcd 28 77 105 7 4 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 77 105 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 77 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 105 (accept_3_4 25 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 105 (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 105 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 77 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 105 (accept_3_4 22 77 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 21 77 105 7 3 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 77 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 105 (accept_3_4 19 77 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 105 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 77 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 105
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 105 (accept_3_4 16 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 105 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 77 105 7 2 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 77 105 (accept_3_4 13 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 77 105 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 77 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 105 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 77 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 105 (accept_3_4 10 77 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 105 (Polychromatic418967fa.accept_18_9_5_15_1_2246
  9 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 77 105 7 1 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 77 105 (Polychromatic418967fa.accept_16_6_13_9_1_4690 6 77 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 105 (Polychromatic418967fa.accept_13_5_12_1_1_2123 5 77 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 105 (accept_3_4 4 77 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 105 (accept_3_4 1 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  105))))))))))))))))))))))))))))) (allB_succ' 30 76 105 (Eq.refl Bool.true) (allA_succ_of_accept 29 76 105 (accept_3_5
  29 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 105
  (Polychromatic418967fa.accept_9_1_4_6_1_5 28 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 76 105 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 76 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 105 (accept_3_5 26 76 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 76 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 105 (Polychromatic418967fa.accept_10_4_6_5_1_74 24
  76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 105 (accept_3_5 23 76
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 105
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 22 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 76 105 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 76 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 105 (accept_3_5 20 76 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 76 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 105 (Polychromatic418967fa.accept_12_6_4_9_1_544
  18 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 105 (accept_3_5 17
  76 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 105
  (Polychromatic418967fa.accept_9_7_4_6_1_273 16 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 76 105 (Polychromatic418967fa.accept_14_1_6_7_1_1936 15 76 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 105 (accept_3_5 14 76 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 76 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 105 (Polychromatic418967fa.accept_9_3_4_6_1_252 12
  76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 105 (accept_3_5 11 76
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 105 (Polychromatic418967fa.accept_9_1_4_6_1_5
  10 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 105
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 105 (accept_3_5 8 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  105 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 76 105 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 76 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 105 (accept_3_5 5 76 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 76 105 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 76 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 105 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 105 (accept_3_5 2 76 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76 105))))))))))))))))))))))))))))))
  (allB_succ' 31 75 105 (Eq.refl Bool.true) (allA_succ_of_gcd 30 75 105 15 2 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 105 (Polychromatic418967fa.accept_9_2_3_6_1_88 29
  75 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 105
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 75 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 75 105 3 9 25 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 75 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 75 105 5 5 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 75 105 3 8 25 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 75 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 75 105 3 7 25 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 75 105 5 4 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 75 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 75 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 105 3 6 25 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 75 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 105
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 75 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 75 105 15 1 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 75 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 75 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 105 3 4 25 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 75 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 75 105 5 2 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 75 105 3 3 25 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 75 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 75 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 105 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 75 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 105 3 2 25 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 75 105 5 1 15 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 105
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 75 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 105 3 1 25 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 75 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 105)))))))))))))))))))))))))))))))
  (allB_succ' 32 74 105 (Eq.refl Bool.true) (allA_succ_of_accept 31 74 105 (accept_3_4 31 74 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 74 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 74 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 74 105 (accept_3_4 28 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  74 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 74 105 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 74 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 105 (accept_3_4 25 74 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 105 (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 74 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 74 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 74 105 (accept_3_4 22 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  74 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 74 105 (Polychromatic418967fa.accept_19_1_17_10_1_4689 20 74 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 105 (accept_3_4 19 74 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 105 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 74 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 74 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 74 105 (accept_3_4 16 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  74 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 74 105 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 74 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 105 (accept_3_4 13 74 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 74 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 74 105 (accept_3_4 10 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  74 105 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 74 105 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 74 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 105 (accept_3_4 7 74 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 105 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 74 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 74 105 (accept_3_4 4 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74
  105 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 74 105 (Polychromatic418967fa.accept_13_2_9_1_1_67 2 74 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 105 (accept_3_4 1 74 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 105)))))))))))))))))))))))))))))))) (allB_succ' 33 73 105 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 73 105 (accept_3_5 32 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  73 105 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 73 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 73 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 73 105 (accept_3_5 29 73 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 73 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 105
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 73 105 (accept_3_5 26 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  73 105 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 73 105 (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 73 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 105 (accept_3_5 23 73 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 73 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 73 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 105
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 73 105 (accept_3_5 20 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  73 105 (Polychromatic418967fa.accept_13_6_8_1_1_2913 19 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 73 105 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 73 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 105 (accept_3_5 17 73 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 105
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 105 (accept_3_5 14 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  73 105 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 73 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 105 (accept_3_5 11 73 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 73 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 105
  (Polychromatic418967fa.accept_13_9_8_1_1_824 9 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 105 (accept_3_5 8 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73
  105 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 105 (Polychromatic418967fa.accept_13_6_8_1_1_2913 6 73 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 105 (accept_3_5 5 73 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 73
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 105 (accept_3_5 2 73 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 105 (Polychromatic418967fa.accept_11_1_7_6_1_378 1
  73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 105)))))))))))))))))))))))))))))))))
  (allB_succ' 34 72 105 (Eq.refl Bool.true) (allA_succ_of_gcd 33 72 105 3 11 24 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 72 105
  (Polychromatic418967fa.accept_13_6_7_1_1_335 32 72 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 105 (Polychromatic418967fa.accept_16_15_8_9_1_2563 31 72 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 105 3 10 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 105 (Polychromatic418967fa.accept_13_3_7_1_1_334 29
  72 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 105
  (Polychromatic418967fa.accept_10_8_2_5_1_596 28 72 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 72 105 3 9 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 72 105 (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 72 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 105 (Polychromatic418967fa.accept_19_6_15_10_1_2170 25 72
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 105 3 8 24 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 105
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 72 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 105 (Polychromatic418967fa.accept_19_3_15_10_1_4688 22 72 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 105 3 7 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 105 (Polychromatic418967fa.accept_16_4_8_9_1_4639 20 72 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 105
  (Polychromatic418967fa.accept_13_6_7_1_1_335 19 72 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 105 3 6 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 105 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 72 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 105 (Polychromatic418967fa.accept_13_3_7_1_1_334 16 72 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 105 3 5 24 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 105
  (Polychromatic418967fa.accept_19_14_15_10_1_3359 14 72 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 72 105 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 72 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 105 3 4 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 105 (Polychromatic418967fa.accept_13_11_7_1_1_1386
  11 72 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 105
  (Polychromatic418967fa.accept_20_10_12_5_1_4687 10 72 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 72 105 3 3 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 72 105 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 72 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 105 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 72 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 105 3 2 24 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 105
  (Polychromatic418967fa.accept_14_5_2_7_1_2804 5 72 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 105 (Polychromatic418967fa.accept_16_4_8_9_1_4639 4 72 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 105 3 1 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 105 (Polychromatic418967fa.accept_22_2_6_17_1_4686 2 72 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 105
  (Polychromatic418967fa.accept_16_1_8_9_1_3462 1 72 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 105)))))))))))))))))))))))))))))))))) (allB_succ' 35 71 105 (Eq.refl Bool.true) (allA_succ_of_accept 34
  71 105 (accept_3_4 34 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 105
  (Polychromatic418967fa.accept_13_7_6_1_1_368 33 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 71 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 105 (accept_3_4 31 71 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 71 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 105 (Polychromatic418967fa.accept_9_2_8_6_1_79 29
  71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 105 (accept_3_4 28 71
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 105
  (Polychromatic418967fa.accept_12_3_11_9_1_193 27 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 71 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 105 (accept_3_4 25 71 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 71 105 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 71 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 105 (Polychromatic418967fa.accept_9_5_8_6_1_281 23
  71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 105 (accept_3_4 22 71
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 105 (Polychromatic418967fa.accept_9_3_8_6_1_80
  21 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 105 (accept_3_4 19 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 105 (Polychromatic418967fa.accept_20_17_11_5_1_4685 17 71 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 105 (accept_3_4 16 71 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 105 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 71 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 105 (accept_3_4 13 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 105 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 71 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 105 (accept_3_4 10 71 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 105 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 71 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 105 (accept_3_4 7 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  105 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 105 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 71 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 105 (accept_3_4 4 71 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 71 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 105 (accept_3_4 1 71 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71 105))))))))))))))))))))))))))))))))))) (allB_succ' 36 70 105
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 70 105 35 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 70 105 (Polychromatic418967fa.accept_13_8_5_1_1_1381 34 70 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 105
  (Polychromatic418967fa.accept_20_13_10_5_1_3338 33 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 105 (accept_3_5 32 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 70 105 5 6 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 70 105 (accept_3_5 29 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 70 105 7 4 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 70 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 105 (accept_3_5 26 70 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 70 105 5 5 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 70 105 (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 70 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 105 (accept_3_5 23 70 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 105 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 70 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 70 105 7 3 10 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 70 105 5 4 14 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 70 105 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 70 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 105 (accept_3_5 17 70 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 70 105 (Polychromatic418967fa.accept_13_3_5_1_1_2144 16 70 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 70 105 5 3 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 70 105 7 2 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 13
  70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 105
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 105 (accept_3_5 11 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70
  105 5 2 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  70 105 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 70 105 (accept_3_5 8 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 70 105 7 1 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 70 105 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 70 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 70 105 5 1 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 70 105 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 70 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 105 (accept_3_5 2 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  105 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 105)))))))))))))))))))))))))))))))))))) (allB_succ' 37 69 105 (Eq.refl Bool.true) (allA_succ_of_gcd 36 69
  105 3 12 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  69 105 (Polychromatic418967fa.accept_20_15_9_5_1_4684 35 69 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 69 105 (Polychromatic418967fa.accept_10_4_9_5_1_84 34 69 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 105 3 11 23 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 105
  (Polychromatic418967fa.accept_17_15_1_3_1_1488 32 69 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 105 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 69 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 105 3 10 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 105 (Polychromatic418967fa.accept_13_3_4_1_1_363 29
  69 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 105
  (Polychromatic418967fa.accept_8_4_5_1_1_299 28 69 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 69 105 3 9 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 69 105 (Polychromatic418967fa.accept_10_6_9_5_1_1046 26 69 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 105 (Polychromatic418967fa.accept_19_6_12_10_1_4683 25 69
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 105 3 8 23 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 105
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 69 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 105 (Polychromatic418967fa.accept_14_8_13_7_1_2798 22 69 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 105 3 7 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 105 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 69 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 105
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 69 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 69 105 3 6 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 69 105 (Polychromatic418967fa.accept_16_1_5_9_1_1649 17 69 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 105 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 69 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 105 3 5 23 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 105
  (Polychromatic418967fa.accept_10_4_9_5_1_84 14 69 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 105 (Polychromatic418967fa.accept_16_13_5_9_1_4682 13 69 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 105 3 4 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 105 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 69 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 105
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 10 69 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 69 105 3 3 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 69 105 (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 69 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 105 (Polychromatic418967fa.accept_20_7_9_5_1_292 7 69 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 105 3 2 23 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 105
  (Polychromatic418967fa.accept_13_5_4_1_1_364 5 69 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 105 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 69 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 105 3 1 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 105 (Polychromatic418967fa.accept_17_2_1_3_1_2357 2 69 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 105
  (Polychromatic418967fa.accept_10_1_9_5_1_83 1 69 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 105))))))))))))))))))))))))))))))))))))) (allB_succ' 38 68 105 (Eq.refl Bool.true) (allA_succ_of_accept
  37 68 105 (accept_3_4 37 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 105
  (Polychromatic418967fa.accept_25_11_18_5_1_4681 36 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 68 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 105 (accept_3_4 34 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 68 105 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 68 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 105 (Polychromatic418967fa.accept_10_2_8_5_1_587
  32 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 105 (accept_3_4 31
  68 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 105
  (Polychromatic418967fa.accept_9_3_5_6_1_253 30 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 68 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 105 (accept_3_4 28 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 68 105 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 68 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 105 (Polychromatic418967fa.accept_9_8_5_6_1_538 26
  68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 105 (accept_3_4 25 68
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 68 105
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 68 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 105 (accept_3_4 22 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 68 105 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 68 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 105 (Polychromatic418967fa.accept_9_2_5_6_1_536 20
  68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 105 (accept_3_4 19 68
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 105
  (Polychromatic418967fa.accept_12_6_8_9_1_553 18 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 68 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 105 (accept_3_4 16 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 68 105 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 68 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 105 (Polychromatic418967fa.accept_16_14_4_9_1_1646
  14 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 105 (accept_3_4 13
  68 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 68 105
  (Polychromatic418967fa.accept_9_3_5_6_1_253 12 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 68 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 105 (accept_3_4 10 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 68 105 (Polychromatic418967fa.accept_14_9_12_7_1_597 9 68 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 105 (Polychromatic418967fa.accept_9_8_5_6_1_538 8
  68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 105 (accept_3_4 7 68 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 105 (Polychromatic418967fa.accept_12_6_8_9_1_553 6
  68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 68 105 (accept_3_4 4 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68
  105 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 68 105 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 105 (accept_3_4 1 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 105)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 67 105 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 67 105 (accept_3_5 38 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  67 105 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 67 105 (Polychromatic418967fa.accept_24_12_19_9_1_4680 36 67 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 67 105 (accept_3_5 35 67 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 67 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 67 105
  (Polychromatic418967fa.accept_10_3_7_5_1_288 33 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 67 105 (accept_3_5 32 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  67 105 (Polychromatic418967fa.accept_14_3_11_7_1_1260 31 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 67 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 67 105 (accept_3_5 29 67 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 67 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 105
  (Polychromatic418967fa.accept_11_5_1_6_1_774 27 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 67 105 (accept_3_5 26 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  67 105 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 67 105 (Polychromatic418967fa.accept_14_10_11_7_1_1955 24 67 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 67 105 (accept_3_5 23 67 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 67 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 105
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 67 105 (accept_3_5 20 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  67 105 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 67 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 105 (accept_3_5 17 67 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 105
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 105 (accept_3_5 14 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  67 105 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 67 105 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 67 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 105 (accept_3_5 11 67 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 105
  (Polychromatic418967fa.accept_13_9_2_1_1_813 9 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 105 (accept_3_5 8 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67
  105 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 67 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 105 (accept_3_5 5 67 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 67 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 105 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 105 (accept_3_5 2 67 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 105 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 67
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  105))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 66 105 (Eq.refl Bool.true) (allA_succ_of_gcd 39 66 105 3 13
  22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 66 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 66 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 66 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 105 3 12 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  66 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 105
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 66 105 3 11 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 66 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 66 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 105 3 10 22 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 66 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 105 3 9 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 66 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 105
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 105 3 8 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 66 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 66 105 3 7 22 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 66 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 105 3 6 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 66 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 105
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 66 105 3 5 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 66 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 66 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 66 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 105 3 4 22 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 66 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 105 3 3 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 66 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 105 3 2 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 66 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 66 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 105 3 1 22 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 66 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 105)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 65 105
  (Eq.refl Bool.true) (allA_succ_of_gcd 40 65 105 5 8 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 65 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 65 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 105 (accept_3_4 37 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 105 (Polychromatic418967fa.accept_17_2_14_3_1_4679 36 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 65 105 5 7 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 65 105 (accept_3_4 34 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 65 105 (Polychromatic418967fa.accept_14_5_9_7_1_590 33 65 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 105 (accept_3_4 31 65 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 65 105 5 6 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 65 105 (Polychromatic418967fa.accept_16_13_1_9_1_2597
  29 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 105 (accept_3_4 28
  65 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 105
  (Polychromatic418967fa.accept_11_5_10_6_1_793 27 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 65 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 65 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 65 105 5 5 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 65 105 (Polychromatic418967fa.accept_16_8_1_9_1_847 24 65 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 105
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 105 (accept_3_4 22 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 65 105 5 4 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 65 105 (accept_3_4 19 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 65 105 (Polychromatic418967fa.accept_16_2_1_9_1_2577 18 65 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 105 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 65 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 105 (accept_3_4 16 65 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 65 105 5 3 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 65 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 14
  65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 105 (accept_3_4 13 65
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 105
  (Polychromatic418967fa.accept_9_3_2_6_1_264 12 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 65 105 (Polychromatic418967fa.accept_17_11_14_3_1_1427 11 65 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 65 105 5 2 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 65 105 (Polychromatic418967fa.accept_18_9_11_15_1_4616 9 65 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 105 (accept_3_4 7 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  105 (Polychromatic418967fa.accept_17_6_14_3_1_4678 6 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 65 105 5 1 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 65 105 (accept_3_4 4 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 65 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 65 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 65 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 105 (accept_3_4 1 65 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65 105))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 64
  105 (Eq.refl Bool.true) (allA_succ_of_accept 41 64 105 (accept_3_5 41 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 64 105 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 64 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 64 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 105 (accept_3_5 38 64 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 64 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 37
  64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 105
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 64 105 (accept_3_5 35 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  64 105 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 64 105 (Polychromatic418967fa.accept_17_16_13_3_1_4677 33 64 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 105 (accept_3_5 32 64 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 64 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 105
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 64 105 (accept_3_5 29 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  64 105 (Polychromatic418967fa.accept_13_2_12_1_1_343 28 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 64 105 (Polychromatic418967fa.accept_14_13_8_7_1_1224 27 64 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 105 (accept_3_5 26 64 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 64 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 105
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 64 105 (accept_3_5 23 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  64 105 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 64 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 64 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 105 (accept_3_5 20 64 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 64 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 105
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 64 105 (accept_3_5 17 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  64 105 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 64 105 (Polychromatic418967fa.accept_13_2_12_1_1_343 15 64 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 105 (accept_3_5 14 64 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 64 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 105
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 64 105 (accept_3_5 11 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  64 105 (Polychromatic418967fa.accept_17_10_13_3_1_1425 10 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 64 105 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 64 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 105 (accept_3_5 8 64 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 64 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 105
  (Polychromatic418967fa.accept_10_6_4_5_1_615 6 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 64 105 (accept_3_5 5 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64
  105 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 64 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 64 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 105 (accept_3_5 2 64 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 64 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64 105)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 63
  105 (Eq.refl Bool.true) (allA_succ_of_gcd 42 63 105 21 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 105 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 63 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 105
  (Polychromatic418967fa.accept_16_8_15_9_1_4676 40 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 63 105 3 13 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 63 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 105 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 63 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 105 3 12 21 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 63 105 7 5 9 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 63 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 63 105 3 11 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 63 105 (Polychromatic418967fa.accept_10_2_3_5_1_996 32 63 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 105 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 63 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 105 3 10 21 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 105
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 63 105 7 4 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 63 105 3 9 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 63 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 105 (Polychromatic418967fa.accept_11_3_8_6_1_788 25 63 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 105 3 8 21 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 105
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 105 21 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 105 (Polychromatic418967fa.accept_13_7_11_1_1_2903 20 63 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 105
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 63 105 3 6 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 63 105 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 63 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 105 (Polychromatic418967fa.accept_13_3_11_1_1_2122 16 63
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 105 3 5 21 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 63 105 7 2 9 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 63 105
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 63 105 3 4 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 63 105 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 63 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 105 3 3 21 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 105
  (Polychromatic418967fa.accept_10_8_3_5_1_613 8 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 63 105 7 1 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 63 105 3 2 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 63 105 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 63 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 105 (Polychromatic418967fa.accept_18_4_9_15_1_3383 4 63 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 105 3 1 21 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 105 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 63 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 63 105))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 62 105
  (Eq.refl Bool.true) (allA_succ_of_accept 43 62 105 (accept_3_4 43 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 62 105 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 62 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 62 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 62 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 105 (accept_3_4 40 62 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 105
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 105 (accept_3_4 37 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 105 (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 105 (accept_3_4 34 62 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 105 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 62 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 105
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 105 (accept_3_4 31 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 62 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 105 (accept_3_4 28 62 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 105
  (Polychromatic418967fa.accept_17_9_11_3_1_2353 26 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 105 (accept_3_4 25 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 105 (Polychromatic418967fa.accept_13_11_10_1_1_1409 24 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 105 (accept_3_4 22 62 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 62 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 105
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 105 (accept_3_4 19 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 105 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 62 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 105 (accept_3_4 16 62 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 105
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 105 (accept_3_4 13 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 105 (accept_3_4 10 62 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 105 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 62 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 105
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 105 (accept_3_4 7 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  105 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 62 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 105 (accept_3_4 4 62 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 105 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 62
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 105 (accept_3_4 1 62 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62 105)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45
  61 105 (Eq.refl Bool.true) (allA_succ_of_accept 44 61 105 (accept_3_5 44 61 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 61 105 (Polychromatic418967fa.accept_17_9_10_3_1_3423 43 61 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 105
  (Polychromatic418967fa.accept_25_17_11_5_1_4675 42 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 105 (accept_3_5 41 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 61 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 105 (accept_3_5 38 61 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 105 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 61 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 105
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 105 (accept_3_5 35 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 105 (Polychromatic418967fa.accept_16_1_13_9_1_2551 33 61 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 105 (accept_3_5 32 61 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 105 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 61 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 105
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 105 (accept_3_5 29 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 105 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 61 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 105 (accept_3_5 26 61 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 105 (Polychromatic418967fa.accept_19_6_4_10_1_3342 25 61 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 105
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 105 (accept_3_5 23 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 61 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 105 (accept_3_5 20 61 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 105 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 61 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 105
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 105 (accept_3_5 17 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 105 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 61 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 105 (accept_3_5 14 61 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 105 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 61 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 105
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 105 (accept_3_5 11 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 105 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 61 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 105 (accept_3_5 8 61 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 105 (Polychromatic418967fa.accept_16_7_13_9_1_1653 7 61 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 105
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 105 (accept_3_5 5 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  105 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 61 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 105 (accept_3_5 2 61 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 105 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 61 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 105))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46
  60 105 (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 105 15 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 105 (Polychromatic418967fa.accept_13_5_8_1_1_2161 44 60 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 105
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 105 3 14 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 105 (Polychromatic418967fa.accept_18_5_6_15_1_3413 41 60 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 105 5 8 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 60 105 3 13 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 60 105 (Polychromatic418967fa.accept_13_12_8_1_1_825 38 60 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 105
  (Polychromatic418967fa.accept_8_5_4_1_1_111 37 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 60 105 3 12 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 60 105 5 7 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 60 105 (Polychromatic418967fa.accept_11_1_5_6_1_397 34 60 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 60 105 3 11 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 60 105 (Polychromatic418967fa.accept_11_10_5_6_1_1842
  32 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 105
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 31 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 105 15 2 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 105 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 60 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 105 (Polychromatic418967fa.accept_17_11_9_3_1_1463 28 60
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 60 105 3 9 20 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 105
  (Polychromatic418967fa.accept_19_7_3_10_1_4674 26 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 60 105 5 5 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 60 105 3 8 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 60 105 (Polychromatic418967fa.accept_11_1_5_6_1_397 23 60 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 105 (Polychromatic418967fa.accept_13_9_8_1_1_824 22 60 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 60 105 3 7 20 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 105 5 4 12 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 105
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 19 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 105 3 6 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 105 (Polychromatic418967fa.accept_14_3_4_7_1_175 17 60 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 105 (Polychromatic418967fa.accept_18_16_6_15_1_3376 16 60
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 105 15 1 4 7 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 105
  (Polychromatic418967fa.accept_27_14_6_24_1_4673 14 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 60 105 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 60 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 105 3 4 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 105 (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 60 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 105 5 2 12 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 105 3 3 20 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 105
  (Polychromatic418967fa.accept_16_8_12_9_1_2569 8 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 60 105 (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 60 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 105 3 2 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 60 105 5 1 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 60 105 (Polychromatic418967fa.accept_16_4_12_9_1_2567 4 60 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 60 105 3 1 20 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 60 105
  (Polychromatic418967fa.accept_16_2_12_9_1_2568 2 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 60 105 (Polychromatic418967fa.accept_11_1_5_6_1_397 1 60 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 105)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 59 105
  (Eq.refl Bool.true) (allA_succ_of_accept 46 59 105 (accept_3_4 46 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 59 105 (Polychromatic418967fa.accept_13_6_7_1_1_335 45 59 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 105 (accept_3_4 43 59 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 42
  59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 105
  (Polychromatic418967fa.accept_10_1_9_5_1_83 41 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 105 (accept_3_4 40 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 105 (accept_3_4 37 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 105 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 59 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 105
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 105 (accept_3_4 34 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 105 (Polychromatic418967fa.accept_20_13_19_5_1_1012 33 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 105 (accept_3_4 31 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 105
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 105 (accept_3_4 28 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 105 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 105 (accept_3_4 25 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 105 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 59 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 105
  (Polychromatic418967fa.accept_37_23_22_31_1_4672 23 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 59 105 (accept_3_4 22 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 59 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 59 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 105 (accept_3_4 19 59 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 105
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 105 (accept_3_4 16 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 105 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 105 (accept_3_4 13 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 59 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 105
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 105 (accept_3_4 10 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 105 (Polychromatic418967fa.accept_18_9_5_15_1_2246 9 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 105 (accept_3_4 7 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 105
  (Polychromatic418967fa.accept_16_5_11_9_1_861 5 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 105 (accept_3_4 4 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  105 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 105 (accept_3_4 1 59 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 105))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 58 105 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 58 105 (accept_3_5 47 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  58 105 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 58 105 (Polychromatic418967fa.accept_18_9_4_15_1_555 45 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 105 (accept_3_5 44 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 58 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 105
  (Polychromatic418967fa.accept_10_2_8_5_1_587 42 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 58 105 (accept_3_5 41 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  58 105 (Polychromatic418967fa.accept_14_12_2_7_1_1243 40 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 58 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 105 (accept_3_5 38 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 58 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 105
  (Polychromatic418967fa.accept_19_17_1_10_1_4671 36 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 105 (accept_3_5 35 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 105 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 105 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 105 (accept_3_5 32 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 105
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 105 (accept_3_5 29 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 105 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 105 (accept_3_5 26 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 58 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 105
  (Polychromatic418967fa.accept_18_6_4_15_1_2276 24 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 105 (accept_3_5 23 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 105 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 105 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 105 (accept_3_5 20 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 105
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 105 (accept_3_5 17 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 105 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 105 (accept_3_5 14 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 58 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 105
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 105 (accept_3_5 11 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 105 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 105 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 105 (accept_3_5 8 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 105
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 105 (accept_3_5 5 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  105 (Polychromatic418967fa.accept_17_4_7_3_1_1417 4 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 58 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 105 (accept_3_5 2 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 58 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 105))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 49 57 105 (Eq.refl Bool.true) (allA_succ_of_gcd 48 57 105 3 16 19 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 105 3 15 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 44
  57 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 105
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 105 3 14 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 57 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 105 3 13 19 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 105 3 12 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  57 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 105
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 105 3 11 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 57 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 105 3 10 19 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 105 3 9 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 57 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 105
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 105 3 8 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 57 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 105 3 7 19 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 105 3 6 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 57 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 105
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 105 3 5 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 57 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 105 3 4 19 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 105 3 3 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 57 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 105
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 105 3 2 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 57 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 105 3 1 19 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 105))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 56
  105 (Eq.refl Bool.true) (allA_succ_of_gcd 49 56 105 7 7 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 56 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 56 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 56 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 56 105 (accept_3_4 46 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  56 105 (Polychromatic418967fa.accept_19_7_18_10_1_1147 45 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 56 105 (Polychromatic418967fa.accept_9_8_2_6_1_875 44 56 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 56 105 (accept_3_4 43 56 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 105 7 6 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 56 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 105 (accept_3_4 40 56 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 56 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 105
  (Polychromatic418967fa.accept_11_5_1_6_1_774 38 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 105 (accept_3_4 37 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 105 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 56 105 7 5 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 56 105 (accept_3_4 34 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 56 105 (Polychromatic418967fa.accept_16_1_8_9_1_3462 33 56 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 105 (Polychromatic418967fa.accept_9_5_2_6_1_265 32 56 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 56 105 (accept_3_4 31 56 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 56 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 30
  56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 56 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 56 105 7 4 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 56 105 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 56 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 105 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 56 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 56 105 (accept_3_4 25 56 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 56 105 (Polychromatic418967fa.accept_10_4_6_5_1_74 24
  56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 56 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 56 105 (accept_3_4 22 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 56
  105 7 3 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  56 105 (Polychromatic418967fa.accept_16_4_8_9_1_4639 20 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 56 105 (accept_3_4 19 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 56 105 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 56 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 56 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 105 (accept_3_4 16 56 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 105 (Polychromatic418967fa.accept_16_15_8_9_1_2563
  15 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 105 7 2 8 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 105 (accept_3_4 13
  56 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 56 105
  (Polychromatic418967fa.accept_9_3_2_6_1_264 12 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 56 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 105 (accept_3_4 10 56 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 56 105 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 56 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 105 (Polychromatic418967fa.accept_9_8_2_6_1_875 8
  56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 56 105 7 1 8 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 56 105
  (Polychromatic418967fa.accept_12_6_8_9_1_553 6 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 105 (accept_3_4 4 56 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 56 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 105 (Polychromatic418967fa.accept_17_2_5_3_1_1416 2
  56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 105 (accept_3_4 1 56 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 105))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 55 105 (Eq.refl Bool.true) (allA_succ_of_gcd 50 55 105 5 10 11 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 55 105
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 105 (accept_3_5 47 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 55 105 5 9 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 55 105 (accept_3_5 44 55 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 105 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 55 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 105 (accept_3_5 41 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 55
  105 5 8 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  55 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 55 105 (accept_3_5 38 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 55 105 (Polychromatic418967fa.accept_13_11_3_1_1_1397 37 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 105 (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 55
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 55 105 5 7 11 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 55 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 55 105 (Polychromatic418967fa.accept_13_7_3_1_1_814 33 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 105 (accept_3_5 32 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 55 105 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 55 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 55 105 5 6 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 55 105 (accept_3_5 29 55 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 105
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 105 (accept_3_5 26 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55
  105 5 5 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  55 105 (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 55 105 (accept_3_5 23 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 55 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 55 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 55 105 5 4 11 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 55 105
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 19 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 105 (accept_3_5 17 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 105 5 3 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 105 (accept_3_5 14 55 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 105 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 55 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 105
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 105 (accept_3_5 11 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55
  105 5 2 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  55 105 (Polychromatic418967fa.accept_20_9_15_5_1_4670 9 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 55 105 (accept_3_5 8 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 55 105 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 55 105 5 1 11 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 55 105
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 105 (accept_3_5 2 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 105 (Polychromatic418967fa.accept_14_1_13_7_1_1205 1 55 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 105)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 54 105 (Eq.refl Bool.true) (allA_succ_of_gcd 51 54 105 3 17 18 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 54 105
  (Polychromatic418967fa.accept_12_2_6_9_1_19 50 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 54 105 (Polychromatic418967fa.accept_10_9_4_5_1_616 49 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 105 3 16 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 105
  (Polychromatic418967fa.accept_10_6_4_5_1_615 46 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 54 105 3 15 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 54 105 (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 105 3 14 18 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 105
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 41 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 54 105 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 54 105 3 13 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 54 105 (Polychromatic418967fa.accept_11_5_10_6_1_793
  38 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 105
  (Polychromatic418967fa.accept_14_9_12_7_1_597 37 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 105 3 12 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 54 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 105 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 54 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 54 105 3 11 18 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 54 105
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 54 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 105 3 10 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 105 (Polychromatic418967fa.accept_10_9_4_5_1_616 29
  54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 105
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 54 105 3 9 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 54 105 (Polychromatic418967fa.accept_10_6_4_5_1_615 26 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 105 (Polychromatic418967fa.accept_13_12_2_1_1_2909 25 54
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 105 3 8 18 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 54 105 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 54 105 3 7 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 54 105 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 54 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 105 3 6 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 105 (Polychromatic418967fa.accept_24_17_6_9_1_4669 17 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 105 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 54 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 54 105 3 5 18 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 54 105
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 105 (Polychromatic418967fa.accept_16_13_6_9_1_2561 13 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 105 3 4 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 105
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 54 105 3 3 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 54 105 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 105 3 2 18 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 105
  (Polychromatic418967fa.accept_11_5_10_6_1_793 5 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 54 105 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 54 105 3 1 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 54 105 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 54 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 105
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 105)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 105 (allA_succ_of_accept 52 53 105
  (accept_3_4 52 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 105
  (Polychromatic418967fa.accept_12_3_5_9_1_176 51 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 53 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 105 (accept_3_4 49 53 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 105 (Polychromatic418967fa.accept_9_2_8_6_1_79 47
  53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 105 (accept_3_4 46 53
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 105
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 45 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 105 (accept_3_4 43 53 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 105 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 105 (Polychromatic418967fa.accept_9_5_8_6_1_281 41
  53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 105 (accept_3_4 40 53
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 105 (Polychromatic418967fa.accept_9_3_8_6_1_80
  39 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 105 (accept_3_4 37 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 105 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 105 (Polychromatic418967fa.accept_17_1_2_3_1_4668 35 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 105 (accept_3_4 34 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 105 (Polychromatic418967fa.accept_16_1_5_9_1_1649 33 53 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 105 (accept_3_4 31 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 105 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 105 (accept_3_4 28 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 105 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 53 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 105 (accept_3_4 25 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 105 (Polychromatic418967fa.accept_14_10_11_7_1_1955 24 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 105 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 105 (accept_3_4 22 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 53 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 105 (accept_3_4 19 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 105 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 105 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 105 (accept_3_4 16 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 105 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 53 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 105 (accept_3_4 13 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 105 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 105 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 105 (accept_3_4 10 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 105 (Polychromatic418967fa.accept_18_9_17_15_1_2267 9 53 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 105 (accept_3_4 7 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  105 (Polychromatic418967fa.accept_18_6_17_15_1_4603 6 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 53 105 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 105 (accept_3_4 4 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 53 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 53 105 (accept_3_4 1 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53
  105))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 105 (allA_succ_of_accept 51 52 105
  (Polychromatic418967fa.accept_30_21_22_15_1_1027 51 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 52 105 (accept_3_5 50 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 52 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 52 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 105 (accept_3_5 47 52 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 105 (Polychromatic418967fa.accept_9_1_7_6_1_75 46
  52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 52 105
  (Polychromatic418967fa.accept_8_5_4_1_1_111 45 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 52 105 (accept_3_5 44 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  52 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 52 105 (Polychromatic418967fa.accept_12_6_4_9_1_544 42 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 105 (accept_3_5 41 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 105 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 52 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 52 105
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 52 105 (accept_3_5 38 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  52 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 52 105 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 105 (accept_3_5 35 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 105 (Polychromatic418967fa.accept_19_15_14_10_1_4667 34 52 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 105
  (Polychromatic418967fa.accept_10_3_2_5_1_295 33 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 52 105 (accept_3_5 32 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  52 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 52 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 105 (accept_3_5 29 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 105 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 52 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 105
  (Polychromatic418967fa.accept_10_7_2_5_1_298 27 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 52 105 (accept_3_5 26 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  52 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 52 105 (Polychromatic418967fa.accept_16_8_4_9_1_4666 24 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 105 (accept_3_5 23 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 105 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 52 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 105
  (Polychromatic418967fa.accept_8_5_4_1_1_111 21 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 52 105 (accept_3_5 20 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  52 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 52 105 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 105 (accept_3_5 17 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 105 (Polychromatic418967fa.accept_23_16_6_13_1_4665 16 52 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 105
  (Polychromatic418967fa.accept_17_15_1_3_1_1488 15 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 105 (accept_3_5 14 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  52 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 52 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 105 (accept_3_5 11 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 105 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 52 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 105
  (Polychromatic418967fa.accept_17_9_1_3_1_4626 9 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 52 105 (accept_3_5 8 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52
  105 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 52 105 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 52 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 105 (accept_3_5 5 52 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 52 105 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 52
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 105 (accept_3_5 2 52 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  105)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 105 (allA_succ_of_accept 50 51 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 105 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 51 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 105 3 16 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 105 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  47 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 105 3 15 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 105 (Polychromatic418967fa.accept_10_4_1_5_1_1018 44 51 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 105 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 51 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 105 3 14 17 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 105
  (Polychromatic418967fa.accept_12_5_3_9_1_541 41 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 105 (Polychromatic418967fa.accept_14_12_9_7_1_2762 40 51 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 105 3 13 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 105
  (Polychromatic418967fa.accept_12_1_3_9_1_174 37 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 105 3 12 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 105 (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 51 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 105 3 11 17 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 105
  (Polychromatic418967fa.accept_22_10_7_17_1_4664 32 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 105 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 51 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 105 3 10 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 105 (Polychromatic418967fa.accept_10_9_1_5_1_594 29
  51 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 105
  (Polychromatic418967fa.accept_13_2_12_1_1_343 28 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 105 3 9 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 105 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 51 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 105 3 8 17 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 105
  (Polychromatic418967fa.accept_11_1_7_6_1_378 23 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 105 3 7 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 105 (Polychromatic418967fa.accept_19_1_13_10_1_4663 20 51
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 105
  (Polychromatic418967fa.accept_10_9_1_5_1_594 19 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 105 3 6 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 105 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 51 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 105 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 51 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 105 3 5 17 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 105 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 51 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 105 3 4 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 105 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 51 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 105 3 3 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 105 (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 51 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 105 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 51 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 105 3 2 17 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 105
  (Polychromatic418967fa.accept_12_5_3_9_1_541 5 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 105 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 51 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 105 3 1 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 105
  (Polychromatic418967fa.accept_11_1_7_6_1_378 1 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 105))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 105 (allA_succ_of_accept 49 50 105
  (accept_3_4 49 50 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 105
  (Polychromatic418967fa.accept_9_3_5_6_1_253 48 50 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 105 (accept_3_4 46 50 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 50 105 5 9 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 50 105 (Polychromatic418967fa.accept_9_8_5_6_1_538 44 50 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 105 (accept_3_4 43 50 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 105 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 50 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 50 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 50 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 105 5 8 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 105 (Polychromatic418967fa.accept_9_2_5_6_1_536 38 50 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 105 (accept_3_4 37 50 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 105
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 50 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 50 105 5 7 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 50 105 (accept_3_4 34 50 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  50 105 (Polychromatic418967fa.accept_13_7_11_1_1_2903 33 50 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 50 105 (Polychromatic418967fa.accept_20_12_10_5_1_4661 32 50 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 105 (accept_3_4 31 50 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 105 5 6 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 50 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 105 (accept_3_4 28 50 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  50 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 105
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 50 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 50 105 5 5 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 50 105 (Polychromatic418967fa.accept_17_7_16_3_1_4660 24 50 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 50 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 105 (accept_3_4 22 50 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 21
  50 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 105 5 4 10 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 105 (accept_3_4 19
  50 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 105
  (Polychromatic418967fa.accept_12_6_2_9_1_537 18 50 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 50 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 105 (accept_3_4 16 50 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 50 105 5 3 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 50 105 (Polychromatic418967fa.accept_19_14_12_10_1_3368 14 50 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 105 (accept_3_4 13 50 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 50 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 105 5 2 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 105 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 50 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 105 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 50 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 105 (accept_3_4 7 50 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 105 (Polychromatic418967fa.accept_12_6_2_9_1_537 6
  50 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 50 105 5 1 10 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 50 105 (accept_3_4 4 50
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 105 (Polychromatic418967fa.accept_4_3_2_1_1_50
  3 50 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 105
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 50 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 50 105 (accept_3_4 1 50 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  105)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 105 (allA_succ_of_accept 48 49 105
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 49 105 (accept_3_5 47 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  49 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 49 105 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 49 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 105 (accept_3_5 44 49 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 105 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 49 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 49 105 7 6 7 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 49 105 (accept_3_5 41 49 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 105
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 105 (accept_3_5 38 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 105 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 105 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 49 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 49 105 7 5 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 49 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 34
  49 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 105
  (Polychromatic418967fa.accept_22_11_5_17_1_4659 33 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 105 (accept_3_5 32 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 105 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 105 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 49 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 105 (accept_3_5 29 49 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 49 105 7 4 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 49 105 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 49 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 105 (accept_3_5 26 49 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 105 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 49 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 105
  (Polychromatic418967fa.accept_10_4_9_5_1_84 24 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 105 (accept_3_5 23 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 49 105 7 3 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 49 105 (accept_3_5 20 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 49 105 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 49 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 105 (Polychromatic418967fa.accept_16_2_1_9_1_2577 18 49 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 105 (accept_3_5 17 49 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  49 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 105
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 49 105 7 2 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 49 105 (Polychromatic418967fa.accept_16_13_1_9_1_2597 13 49 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 105 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 49 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 105 (accept_3_5 11 49 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 10
  49 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 105
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 105 (accept_3_5 8 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 49 105
  7 1 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 49 105
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 105 (accept_3_5 5 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  105 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 105 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 49 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 105 (accept_3_5 2 49 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 105 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 49 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 105))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 105 (allA_succ_of_accept 47 48 105 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 48 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 46
  48 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 105 3 15 16 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 105
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 48 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 48 105 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 48 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 105 3 14 16 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  48 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 105
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 48 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 48 105 3 13 16 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 48 105 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 48 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 48 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 105 3 12 16 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 105
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 48 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 105 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 48 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 48 105 3 11 16 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 48 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  48 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 105
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 48 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 105 3 10 16 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 105 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 48 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 48 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 48 105 3 9 16 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 105
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 48 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 48 105 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 48 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 105 3 8 16 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 48 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 105
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 48 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 48 105 3 7 16 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 48 105 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 48 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 48 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 105 3 6 16 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 105
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 48 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 105 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 48 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 105 3 5 16 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 48 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 105
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 48 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 105 3 4 16 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 105 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 48 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 48 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 105 3 3 16 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 105
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 48 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 48 105 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 48 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 105 3 2 16 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 48 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 105
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 48 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 48 105 3 1 16 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 48 105 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 48 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 48 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  105)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 105 (allA_succ_of_accept 46 47 105 (accept_3_4 46 47
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 105
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 105 (accept_3_4 43 47 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 105 (Polychromatic418967fa.accept_9_5_2_6_1_265 41
  47 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 105 (accept_3_4 40 47
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 105
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 105 (accept_3_4 37 47 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 105 (Polychromatic418967fa.accept_22_14_3_17_1_4658 36 47 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 105
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 105 (accept_3_4 34 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 105 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 105 (accept_3_4 31 47 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 105
  (Polychromatic418967fa.accept_20_9_7_5_1_2114 29 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 105 (accept_3_4 28 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 105 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 105 (accept_3_4 25 47 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 105 (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 47 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 105
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 105 (accept_3_4 22 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 105 (accept_3_4 19 47 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 105
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 105 (accept_3_4 16 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 105 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 105 (accept_3_4 13 47 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 47 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 105
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 105 (accept_3_4 10 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 105 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 105 (accept_3_4 7 47 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 105
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 105 (accept_3_4 4 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  105 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 47 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 105 (accept_3_4 1 47 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 105))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 105 (allA_succ_of_accept 45
  46 105 (Polychromatic418967fa.accept_13_6_7_1_1_335 45 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 46 105 (accept_3_5 44 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 46 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 105 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 46 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 105 (accept_3_5 41 46 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 105 (Polychromatic418967fa.accept_9_4_1_6_1_284 40
  46 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 105 (accept_3_5 38 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 105 (Polychromatic418967fa.accept_16_4_14_9_1_4657 36 46 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 105 (accept_3_5 35 46 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 105 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 46 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 105
  (Polychromatic418967fa.accept_22_11_2_17_1_4656 33 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 105 (accept_3_5 32 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 46 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 105 (accept_3_5 29 46 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 105 (Polychromatic418967fa.accept_22_6_2_17_1_4655 28 46 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 105 (accept_3_5 26 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 105 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 46 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 105 (accept_3_5 23 46 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 105 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 46 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 105
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 105 (accept_3_5 20 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 105 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 46 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 105 (accept_3_5 17 46 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 105 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 46 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 105 (accept_3_5 14 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 46 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 105 (accept_3_5 11 46 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 105 (Polychromatic418967fa.accept_14_10_4_7_1_1214 10 46 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 105
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 105 (accept_3_5 8 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  105 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 105 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 46 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 105 (accept_3_5 5 46 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 105 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 46 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 105 (accept_3_5 2 46 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 46
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  105)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 105 (allA_succ_of_accept 44 45 105
  (Polychromatic418967fa.accept_8_4_5_1_1_299 44 45 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 105 (Polychromatic418967fa.accept_17_9_11_3_1_2353 43 45 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 105 3 14 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 105 (Polychromatic418967fa.accept_13_2_6_1_1_3807
  41 45 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 105 5 8 9 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 45 105 3 13 15 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 105
  (Polychromatic418967fa.accept_11_5_1_6_1_774 38 45 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 105 (Polychromatic418967fa.accept_16_5_13_9_1_2594 37 45 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 105 3 12 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 45 105 5 7 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 105 (Polychromatic418967fa.accept_13_8_6_1_1_3808
  34 45 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 105 3 11 15 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 105
  (Polychromatic418967fa.accept_14_4_3_7_1_3702 32 45 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 105 (Polychromatic418967fa.accept_13_5_6_1_1_822 31 45 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 105 15 2 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 105 (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 45 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 105
  (Polychromatic418967fa.accept_8_4_5_1_1_299 28 45 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 45 105 3 9 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 45 105 (Polychromatic418967fa.accept_17_9_11_3_1_2353 26 45 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 105 5 5 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 45 105 3 8 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 105 (Polychromatic418967fa.accept_16_7_13_9_1_1653 23 45 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 105
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 22 45 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 105 3 7 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 45 105 5 4 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 45 105 (Polychromatic418967fa.accept_17_2_11_3_1_4654 19 45 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 105 3 6 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 105 (Polychromatic418967fa.accept_16_1_13_9_1_2551 17 45 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 105
  (Polychromatic418967fa.accept_11_5_1_6_1_774 16 45 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 45 105 15 1 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 45 105 (Polychromatic418967fa.accept_17_14_11_3_1_4653 14 45 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 105 (Polychromatic418967fa.accept_25_13_20_5_1_4652 13 45
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 105 3 4 15 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 105
  (Polychromatic418967fa.accept_14_11_3_7_1_604 11 45 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 45 105 5 2 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 45 105 3 3 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 45 105 (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 45 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 105 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 45 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 105 3 2 15 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 45 105 5 1 9 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 105
  (Polychromatic418967fa.accept_8_4_5_1_1_299 4 45 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 105 3 1 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 105 (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 45 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 105 (Polychromatic418967fa.accept_16_1_13_9_1_2551 1 45 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  105))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 105 (allA_succ_of_accept 43 44 105 (accept_3_4 43 44
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 105
  (Polychromatic418967fa.accept_12_6_8_9_1_553 42 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 105 (accept_3_4 40 44 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 44 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 105 (Polychromatic418967fa.accept_9_2_8_6_1_79 38
  44 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 105 (accept_3_4 37 44
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 105
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 105 (accept_3_4 34 44 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 105 (Polychromatic418967fa.accept_14_5_2_7_1_2804 33 44 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 105 (Polychromatic418967fa.accept_9_5_8_6_1_281 32
  44 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 105 (accept_3_4 31 44
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 105 (Polychromatic418967fa.accept_9_3_8_6_1_80
  30 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 44 105 (accept_3_4 28 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  44 105 (Polychromatic418967fa.accept_30_27_14_15_1_4651 27 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 44 105 (Polychromatic418967fa.accept_10_6_4_5_1_615 26 44 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 105 (accept_3_4 25 44 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 105 (Polychromatic418967fa.accept_16_8_12_9_1_2569 24 44 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 44 105 (accept_3_4 22 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  44 105 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 44 105 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 44 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 105 (accept_3_4 19 44 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 105 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 44 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 44 105 (accept_3_4 16 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  44 105 (Polychromatic418967fa.accept_19_15_6_10_1_4650 15 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 44 105 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 44 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 105 (accept_3_4 13 44 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 44 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 44 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 44 105 (accept_3_4 10 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  44 105 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 44 105 (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 44 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 105 (accept_3_4 7 44 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 105 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 44 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 105 (accept_3_4 4 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  105 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 44 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 105 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 44 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 105 (accept_3_4 1 44 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 105)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 105 (allA_succ_of_accept 42 43
  105 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 105 (accept_3_5 41 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 43 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 105 (accept_3_5 38 43 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 105 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 43 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 105
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 105 (accept_3_5 35 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 105 (Polychromatic418967fa.accept_19_14_5_10_1_4610 33 43 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 105 (accept_3_5 32 43 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 105 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 43 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 105 (accept_3_5 29 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 105 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 43 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 105 (accept_3_5 26 43 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 105 (Polychromatic418967fa.accept_24_1_19_9_1_4649 25 43 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 105
  (Polychromatic418967fa.accept_30_24_13_15_1_4648 24 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 43 105 (accept_3_5 23 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 43 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 43 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 105 (accept_3_5 20 43 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 105 (Polychromatic418967fa.accept_9_1_7_6_1_75 19
  43 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 105 (accept_3_5 17 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 105 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 43 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 105 (accept_3_5 14 43 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 105 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 43 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 105
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 105 (accept_3_5 11 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 105 (Polychromatic418967fa.accept_25_9_18_5_1_4647 9 43 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 105 (accept_3_5 8 43 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 105 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 43 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 105 (accept_3_5 5 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  105 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 43 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 105 (accept_3_5 2 43 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 105 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 43 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 105))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 105
  (allA_succ_of_accept 41 42 105 (Polychromatic418967fa.accept_13_2_3_1_1_3823 41 42 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 105 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 42 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 105 3 13 14 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 105
  (Polychromatic418967fa.accept_10_8_2_5_1_596 38 42 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 42 105 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 42 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 105 3 12 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 42 105 7 5 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 42 105 (Polychromatic418967fa.accept_12_10_6_9_1_549
  34 42 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 42 105 3 11 14 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 42 105
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 42 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 105 3 10 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 105 (Polychromatic418967fa.accept_17_12_8_3_1_4646
  29 42 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 105 7 4 6 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 105 3 9 14 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 42 105
  (Polychromatic418967fa.accept_12_2_6_9_1_19 26 42 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 42 105 (Polychromatic418967fa.accept_11_3_9_6_1_105 25 42 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 105 3 8 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 105
  (Polychromatic418967fa.accept_12_10_6_9_1_549 22 42 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 42 105 21 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 42 105 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 42 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 105 3 6 14 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 105
  (Polychromatic418967fa.accept_10_7_2_5_1_298 17 42 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 105 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 42 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 42 105 3 5 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 42 105 7 2 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 105 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 42 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 105 3 4 14 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 105 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 42 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 42 105 3 3 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 42 105 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 42 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 42 105 7 1 6 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 42 105 3 2 14 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 105
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 42 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 105 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 42 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 105 3 1 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 105 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 42 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 105
  (Polychromatic418967fa.accept_16_1_10_9_1_4645 1 42 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 105)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 105 (allA_succ_of_accept 40 41 105
  (accept_3_4 40 41 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 105
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 41 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 41 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 105 (accept_3_4 37 41 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 105 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 41 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 105 (Polychromatic418967fa.accept_9_8_5_6_1_538 35
  41 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 105 (accept_3_4 34 41
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 105
  (Polychromatic418967fa.accept_17_16_7_3_1_4644 33 41 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 105 (accept_3_4 31 41 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 41 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 105 (Polychromatic418967fa.accept_9_2_5_6_1_536 29
  41 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 105 (accept_3_4 28 41
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 105
  (Polychromatic418967fa.accept_12_3_5_9_1_176 27 41 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 41 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 41 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 105 (accept_3_4 25 41 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 41 105 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 41 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 105 (Polychromatic418967fa.accept_20_3_1_5_1_4643
  23 41 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 105 (accept_3_4 22
  41 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 105
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 41 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 105 (accept_3_4 19 41 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 105 (Polychromatic418967fa.accept_30_18_11_15_1_4642 18 41 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 105
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 41 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 105 (accept_3_4 16 41 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 105 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 41 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 41 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 105 (accept_3_4 13 41 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 41 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 105
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 41 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 105 (accept_3_4 10 41 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 105 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 41 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 105 (accept_3_4 7 41 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 105 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 41 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 105
  (Polychromatic418967fa.accept_19_5_3_10_1_4641 5 41 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 105 (accept_3_4 4 41 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  105 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 41 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 41 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 105 (accept_3_4 1 41 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 105))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 105 (allA_succ_of_accept 39 40 105
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 40 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 105 (accept_3_5 38 40 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 105 (Polychromatic418967fa.accept_16_4_8_9_1_4639 36 40 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 40 105 5 7 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 40 105 (Polychromatic418967fa.accept_9_7_4_6_1_273 34
  40 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 105
  (Polychromatic418967fa.accept_14_5_12_7_1_2767 33 40 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 105 (accept_3_5 32 40 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 40 105 5 6 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 40 105 (accept_3_5 29 40 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 40 105 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 40 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 105 (Polychromatic418967fa.accept_18_9_4_15_1_555 27 40 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 105 (accept_3_5 26 40 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 40 105 5 5 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 40 105 (Polychromatic418967fa.accept_18_6_4_15_1_2276
  24 40 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 105 (accept_3_5 23
  40 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 105
  (Polychromatic418967fa.accept_17_5_6_3_1_4640 22 40 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 40 105 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 40 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 105 5 4 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 40 105
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 40 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 40 105 (accept_3_5 17 40 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  40 105 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 40 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 40 105 5 3 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 40 105 (accept_3_5 14 40 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 40 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 105 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 40 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 105 (accept_3_5 11 40 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 105 5 2 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 105 (Polychromatic418967fa.accept_14_9_12_7_1_597 9
  40 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 40 105 (accept_3_5 8 40 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 40 105
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 40 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 40 105 5 1 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 40 105 (Polychromatic418967fa.accept_16_4_8_9_1_4639 4 40 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 105 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 40 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 105 (accept_3_5 2 40 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  105)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 105 (allA_succ_of_accept 38 39 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 39 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 105 3 12 13 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  39 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 105 3 11 13 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 39 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 39 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 105 3 10 13 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 39 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 39 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 105 3 9 13 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 105
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 39 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 105 3 8 13 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 39 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 105 3 7 13 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 39 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 39 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 105 3 6 13 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 39 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 105
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 39 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 105 3 5 13 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 39 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 105 3 4 13 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 39 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 105 3 3 13 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 39 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 105
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 39 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 105 3 2 13 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 105 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 39 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 39 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 105 3 1 13 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 39 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 105))))))))))))))))))))))))))))))))))))))) (allB_succ 38 105
  (allA_succ_of_accept 37 38 105 (accept_3_4 37 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 105 (Polychromatic418967fa.accept_20_16_18_5_1_4638 36 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 105 (accept_3_4 34 38 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 105 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 38 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 105
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 105 (accept_3_4 31 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 38 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 105 (accept_3_4 28 38 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 105
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 105 (accept_3_4 25 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 105 (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 105 (accept_3_4 22 38 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 38 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 105
  (Polychromatic418967fa.accept_25_20_13_5_1_4637 20 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 105 (accept_3_4 19 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 105 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 38 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 105 (accept_3_4 16 38 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 105
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 105 (accept_3_4 13 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 105 (accept_3_4 10 38 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 105 (Polychromatic418967fa.accept_30_9_8_15_1_4636 9 38 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 105
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 105 (accept_3_4 7 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  105 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 38 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 38 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 105 (accept_3_4 4 38 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 105 (Polychromatic418967fa.accept_10_2_8_5_1_587 2
  38 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 105 (accept_3_4 1 38 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 105)))))))))))))))))))))))))))))))))))))) (allB_succ 37 105
  (allA_succ_of_accept 36 37 105 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 37 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 105 (accept_3_5 35 37 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 37 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 105 (Polychromatic418967fa.accept_10_3_7_5_1_288
  33 37 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 105 (accept_3_5 32
  37 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 105
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 37 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 37 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 105 (accept_3_5 29 37 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 105 (Polychromatic418967fa.accept_12_3_1_9_1_202
  27 37 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 105 (accept_3_5 26
  37 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 105
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 37 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 105 (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 37 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 105 (accept_3_5 23 37 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 37 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 21
  37 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 105 (accept_3_5 20 37
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 105
  (Polychromatic418967fa.accept_14_5_9_7_1_590 19 37 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 105 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 37 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 105 (accept_3_5 17 37 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 105 (Polychromatic418967fa.accept_12_3_1_9_1_202
  15 37 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 105 (accept_3_5 14
  37 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 105
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 37 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 37 105 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 37 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 105 (accept_3_5 11 37 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 37 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 37 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 105 (Polychromatic418967fa.accept_13_9_11_1_1_1375
  9 37 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 105 (accept_3_5 8 37
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 105 (Polychromatic418967fa.accept_9_7_1_6_1_261
  7 37 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 105
  (Polychromatic418967fa.accept_22_6_15_17_1_4635 6 37 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 105 (accept_3_5 5 37 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  105 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 37 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 105 (accept_3_5 2 37 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 105 (Polychromatic418967fa.accept_16_1_5_9_1_1649 1 37 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 105))))))))))))))))))))))))))))))))))))) (allB_succ 36 105
  (allA_succ_of_accept 35 36 105 (Polychromatic418967fa.accept_13_9_10_1_1_1389 35 36 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 105 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 36 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 105 3 11 12 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 105
  (Polychromatic418967fa.accept_25_7_11_5_1_4634 32 36 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 105 (Polychromatic418967fa.accept_10_1_6_5_1_304 31 36 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 105 3 10 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 105 (Polychromatic418967fa.accept_8_5_4_1_1_111 29
  36 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 105
  (Polychromatic418967fa.accept_16_12_4_9_1_4633 28 36 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 36 105 3 9 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 36 105 (Polychromatic418967fa.accept_19_7_17_10_1_4630 26 36 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 105 (Polychromatic418967fa.accept_22_3_14_17_1_3159 25 36
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 105 3 8 12 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 105
  (Polychromatic418967fa.accept_19_4_17_10_1_4632 23 36 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 105 (Polychromatic418967fa.accept_13_9_10_1_1_1389 22 36 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 36 105 3 7 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 36 105 (Polychromatic418967fa.accept_11_9_3_6_1_797 20 36 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 105
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 36 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 105 3 6 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 105 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 36 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 105 (Polychromatic418967fa.accept_25_16_11_5_1_4631 16 36
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 105 3 5 12 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 105
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 36 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 105 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 36 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 105 3 4 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 105 (Polychromatic418967fa.accept_10_1_6_5_1_304 11 36 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 105
  (Polychromatic418967fa.accept_20_10_16_5_1_3311 10 36 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 36 105 3 3 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 36 105 (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 36 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 105 (Polychromatic418967fa.accept_19_7_17_10_1_4630 7 36 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 105 3 2 12 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 105
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 36 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 105 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 36 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 36 105 3 1 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 36 105 (Polychromatic418967fa.accept_19_2_17_10_1_4629 2 36 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 105
  (Polychromatic418967fa.accept_10_1_6_5_1_304 1 36 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 105)))))))))))))))))))))))))))))))))))) (allB_succ 35 105 (allA_succ_of_accept 34 35 105 (accept_3_4 34
  35 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 105
  (Polychromatic418967fa.accept_20_13_15_5_1_4628 33 35 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 105 (accept_3_4 31 35 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 35 105 5 6 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 35 105 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 35 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 35 105 7 4 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 35 105 (Polychromatic418967fa.accept_12_3_11_9_1_193
  27 35 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 35 105 5 5 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 35 105 (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 35 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 105 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 35 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 105 (accept_3_4 22 35 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 35 105 7 3 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 35 105 5 4 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 35 105 (accept_3_4 19 35 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 105
  (Polychromatic418967fa.accept_20_17_15_5_1_4627 17 35 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 105 (accept_3_4 16 35 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 35
  105 5 3 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 35
  105 7 2 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13
  35 105 (accept_3_4 13 35 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 105
  (Polychromatic418967fa.accept_9_3_8_6_1_80 12 35 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 35 105 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 35 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 35 105 5 2 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 35 105 (Polychromatic418967fa.accept_17_9_1_3_1_4626 9 35 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 35 105 7 1 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 35 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 105 5 1 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 105 (accept_3_4 4 35 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 35 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 105 (accept_3_4 1 35 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 105))))))))))))))))))))))))))))))))))) (allB_succ 34 105
  (allA_succ_of_accept 33 34 105 (Polychromatic418967fa.accept_13_7_8_1_1_2145 33 34 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 34 105 (accept_3_5 32 34 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 34 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 30
  34 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 105 (accept_3_5 29 34
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 105 (Polychromatic418967fa.accept_9_1_7_6_1_75
  28 34 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 105 (accept_3_5 26 34 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 34 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 105 (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 34 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 105 (accept_3_5 23 34 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 105 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 34 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 105
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 34 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 105 (accept_3_5 20 34 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 105 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 34 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 105 (accept_3_5 17 34 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 105 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 34 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 105 (accept_3_5 14 34 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 34 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 34 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 105 (accept_3_5 11 34 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 105 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 34 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 105
  (Polychromatic418967fa.accept_10_9_4_5_1_616 9 34 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 105 (accept_3_5 8 34 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  105 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 105 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 34 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 105 (accept_3_5 5 34 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 105 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 34 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 105 (accept_3_5 2 34 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 34
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 105))))))))))))))))))))))))))))))))))
  (allB_succ 33 105 (allA_succ_of_accept 32 33 105 (Polychromatic418967fa.accept_10_2_3_5_1_996 32 33 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 105
  (Polychromatic418967fa.accept_19_12_14_10_1_4625 31 33 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 33 105 3 10 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 33 105 (Polychromatic418967fa.accept_13_3_7_1_1_334 29 33 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 105
  (Polychromatic418967fa.accept_10_8_3_5_1_613 28 33 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 33 105 3 9 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 33 105 (Polychromatic418967fa.accept_14_12_5_7_1_2010 26 33 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 105 (Polychromatic418967fa.accept_19_6_14_10_1_4624 25 33
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 105 3 8 11 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 105
  (Polychromatic418967fa.accept_14_9_5_7_1_1251 23 33 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 105 (Polychromatic418967fa.accept_10_2_3_5_1_996 22 33 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 33 105 3 7 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 105 (Polychromatic418967fa.accept_19_1_14_10_1_4619 20 33
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 105
  (Polychromatic418967fa.accept_13_6_7_1_1_335 19 33 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 33 105 3 6 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 33 105 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 33 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 105 (Polychromatic418967fa.accept_13_3_7_1_1_334 16 33 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 105 3 5 11 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 105
  (Polychromatic418967fa.accept_23_14_10_13_1_4623 14 33 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 33 105 (Polychromatic418967fa.accept_16_13_1_9_1_2597 13 33 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 105 3 4 11 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 33 105
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 33 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 105 (Polychromatic418967fa.accept_16_10_1_9_1_4622 10 33 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 105 3 3 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 105 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 33 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 105
  (Polychromatic418967fa.accept_10_7_3_5_1_301 7 33 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 33 105 3 2 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 33 105 (Polychromatic418967fa.accept_16_5_1_9_1_4621 5 33 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 105 (Polychromatic418967fa.accept_17_4_16_3_1_4620 4 33 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 105 3 1 11 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 105
  (Polychromatic418967fa.accept_10_2_3_5_1_996 2 33 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 33 105 (Polychromatic418967fa.accept_19_1_14_10_1_4619 1 33 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 33 105))))))))))))))))))))))))))))))))) (allB_succ 32 105
  (allA_succ_of_accept 31 32 105 (accept_3_4 31 32 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  32 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 32 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 32 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 105 (accept_3_4 28 32 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 105 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 32 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 105
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 32 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 105 (accept_3_4 25 32 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 105 (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 32 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 105 (accept_3_4 22 32 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 32 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 105
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 32 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 105 (accept_3_4 19 32 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 105 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 32 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 105 (accept_3_4 16 32 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 105 (Polychromatic418967fa.accept_13_2_6_1_1_3807 15 32 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 105
  (Polychromatic418967fa.accept_17_14_15_3_1_4618 14 32 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 105 (accept_3_4 13 32 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 32 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 105 (accept_3_4 10 32 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 105 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 32 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 105
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 32 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 105 (accept_3_4 7 32 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  105 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 32 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 105 (accept_3_4 4 32 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 32 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 105 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  32 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 105 (accept_3_4 1 32 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 105)))))))))))))))))))))))))))))))) (allB_succ 31 105
  (allA_succ_of_accept 30 31 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 105 (accept_3_5 29 31 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 105 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  27 31 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 105 (accept_3_5 26
  31 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 105
  (Polychromatic418967fa.accept_9_7_4_6_1_273 25 31 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 105 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 31 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 105 (accept_3_5 23 31 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 105 (Polychromatic418967fa.accept_9_3_4_6_1_252 21
  31 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 105 (accept_3_5 20 31
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 105 (Polychromatic418967fa.accept_9_1_4_6_1_5
  19 31 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 105 (accept_3_5 17 31 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 105 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 31 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 105 (accept_3_5 14 31 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 105 (Polychromatic418967fa.accept_27_13_4_24_1_4617 13 31 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 105
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 31 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 105 (accept_3_5 11 31 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 105 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 31 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 105 (accept_3_5 8 31 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 105 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 31 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 105 (accept_3_5 5 31 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  105 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 105 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 31 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 105 (accept_3_5 2 31 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 105 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 31 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 105))))))))))))))))))))))))))))))) (allB_succ 30 105
  (allA_succ_of_accept 29 30 105 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 30 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 30 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 105 3 9 10 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 105
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 30 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 30 105 5 5 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 30 105 3 8 10 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 30 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 30 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 30 105 3 7 10 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 30 105 5 4 6 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 105 3 6 10 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 30 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 105 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 30 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 105 15 1 2 7 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 105
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 30 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 30 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 30 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 105 3 4 10 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 105 5 2 6 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 105 3 3 10 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 105
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 30 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 105 3 2 10 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 105 5 1 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 30 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 30 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 30 105 3 1 10 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 30 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 30 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 30 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 105)))))))))))))))))))))))))))))) (allB_succ 29 105 (allA_succ_of_accept
  28 29 105 (accept_3_4 28 29 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 105
  (Polychromatic418967fa.accept_12_3_5_9_1_176 27 29 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 29 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 105 (accept_3_4 25 29 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 105 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 29 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 105 (Polychromatic418967fa.accept_9_5_2_6_1_265 23
  29 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 105 (accept_3_4 22 29
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 105
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 29 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 105 (accept_3_4 19 29 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 105 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 29 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 105 (Polychromatic418967fa.accept_9_8_2_6_1_875 17
  29 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 105 (accept_3_4 16 29
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 105
  (Polychromatic418967fa.accept_12_3_5_9_1_176 15 29 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 29 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 105 (accept_3_4 13 29 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 105 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 29 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 105 (Polychromatic418967fa.accept_10_1_9_5_1_83 11
  29 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 105 (accept_3_4 10 29
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 105
  (Polychromatic418967fa.accept_18_9_11_15_1_4616 9 29 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 29 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 105 (accept_3_4 7 29 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 29 105 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 29 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 105 (Polychromatic418967fa.accept_9_5_2_6_1_265 5
  29 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 105 (accept_3_4 4 29 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 3
  29 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 29 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 29 105 (accept_3_4 1 29 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29
  105))))))))))))))))))))))))))))) (allB_succ 28 105 (allA_succ_of_accept 27 28 105
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 28 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 105 (accept_3_5 26 28 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 105 (Polychromatic418967fa.accept_16_8_12_9_1_2569 24 28 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 105 (accept_3_5 23 28 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 105 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 28 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 28 105 7 3 4 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 28 105 (accept_3_5 20 28 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 28 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  28 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 105
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 28 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 28 105 (accept_3_5 17 28 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  28 105 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 28 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 28 105 (Polychromatic418967fa.accept_19_15_9_10_1_4615 15 28 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 105 7 2 4 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 105
  (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 28 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 28 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 105 (accept_3_5 11 28 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 28 105 (Polychromatic418967fa.accept_17_10_11_3_1_3442 10 28 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 105
  (Polychromatic418967fa.accept_13_9_2_1_1_813 9 28 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 105 (accept_3_5 8 28 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 28 105
  7 1 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 28 105
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 28 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 28 105 (accept_3_5 5 28 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28
  105 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 28 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 28 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 28 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 105 (accept_3_5 2 28 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 28 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 105)))))))))))))))))))))))))))) (allB_succ 27 105
  (allA_succ_of_accept 26 27 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 105 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 27 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 105 3 8 9 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 105
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 27 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 105 3 7 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 105 (Polychromatic418967fa.accept_14_6_13_7_1_2015 20 27 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 105
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 27 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 27 105 3 6 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 27 105 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 27 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 105 (Polychromatic418967fa.accept_18_16_9_15_1_4614 16 27
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 105 3 5 9 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 105 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 27 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 105 3 4 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 105 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 27 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 27 105 3 3 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 27 105 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 27 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 105 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 27 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 105 3 2 9 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 105
  (Polychromatic418967fa.accept_12_5_3_9_1_541 5 27 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 105 (Polychromatic418967fa.accept_16_4_11_9_1_1631 4 27 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 105 3 1 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 105
  (Polychromatic418967fa.accept_11_1_5_6_1_397 1 27 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 105))))))))))))))))))))))))))) (allB_succ 26 105 (allA_succ_of_accept 25 26 105 (accept_3_4 25 26 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 105 (Polychromatic418967fa.accept_10_4_6_5_1_74 24
  26 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 26 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 26 105 (accept_3_4 22 26 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  26 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 26 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 26 105 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 26 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 105 (accept_3_4 19 26 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 105 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 26 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 26 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 26 105 (accept_3_4 16 26 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  26 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 26 105 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 26 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 105 (accept_3_4 13 26 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 26 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 105 (accept_3_4 10 26 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  26 105 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 26 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 26 105 (Polychromatic418967fa.accept_25_8_1_5_1_4613 8 26 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 105 (accept_3_4 7 26 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 105 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 26 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 26 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 26 105 (accept_3_4 4 26 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26
  105 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 26 105 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 26 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 105 (accept_3_4 1 26 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 105)))))))))))))))))))))))))) (allB_succ 25 105 (allA_succ_of_accept 24 25 105
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 25 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 105 (accept_3_5 23 25 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 25 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 25 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 105 5 4 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 105 (Polychromatic418967fa.accept_9_1_7_6_1_75 19
  25 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 105
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 25 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 105 (accept_3_5 17 25 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 25 105 5 3 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 25 105 (accept_3_5 14 25 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 25 105 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 25 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 25 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 105 (accept_3_5 11 25 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25 105 5 2 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25 105 (Polychromatic418967fa.accept_11_9_3_6_1_797 9
  25 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 105 (accept_3_5 8 25 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 105 (Polychromatic418967fa.accept_27_7_25_24_1_4612
  7 25 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 105
  (Polychromatic418967fa.accept_24_6_1_9_1_4611 6 25 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 25 105 5 1 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 25 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 25 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 105 (accept_3_5 2 25 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 105 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 25
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 105))))))))))))))))))))))))) (allB_succ
  24 105 (allA_succ_of_accept 23 24 105 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 24 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 105 (Polychromatic418967fa.accept_13_9_11_1_1_1375
  22 24 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 105 3 7 8 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 105
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 20 24 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 105 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 24 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 105 3 6 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 105 (Polychromatic418967fa.accept_14_3_10_7_1_3773 17 24 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 105
  (Polychromatic418967fa.accept_10_6_4_5_1_615 16 24 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 105 3 5 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 105 (Polychromatic418967fa.accept_19_14_5_10_1_4610 14 24 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 105 (Polychromatic418967fa.accept_19_13_5_10_1_4609 13 24
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 105 3 4 8 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 105
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 24 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 105 (Polychromatic418967fa.accept_13_10_11_1_1_2152 10 24 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 105 3 3 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 105 (Polychromatic418967fa.accept_13_8_11_1_1_3789 8 24 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 105
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 24 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 105 3 2 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 105 (Polychromatic418967fa.accept_18_5_6_15_1_3413 5 24 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 105 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 24 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 105 3 1 8 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 105
  (Polychromatic418967fa.accept_19_2_5_10_1_4608 2 24 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 105 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 24 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 105)))))))))))))))))))))))) (allB_succ 23 105 (allA_succ_of_accept 22 23
  105 (accept_3_4 22 23 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 105
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 23 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 105 (accept_3_4 19 23 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 105 (Polychromatic418967fa.accept_9_8_5_6_1_538 17
  23 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 105 (accept_3_4 16 23
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 105
  (Polychromatic418967fa.accept_12_3_11_9_1_193 15 23 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 105 (accept_3_4 13 23 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 23 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 105 (Polychromatic418967fa.accept_9_2_5_6_1_536 11
  23 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 105 (accept_3_4 10 23
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 105
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 23 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 105 (accept_3_4 7 23 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 105 (Polychromatic418967fa.accept_11_5_1_6_1_774 5
  23 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 105 (accept_3_4 4 23 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  23 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 105 (accept_3_4 1 23 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  105))))))))))))))))))))))) (allB_succ 22 105 (allA_succ_of_accept 21 22 105
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 22 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 105 (accept_3_5 20 22 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 105 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 22 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 105 (accept_3_5 17 22 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 105 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 22 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 105
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 105 (accept_3_5 14 22 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 22 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 105 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 22 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 105 (accept_3_5 11 22 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 105 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 22 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 105
  (Polychromatic418967fa.accept_18_9_4_15_1_555 9 22 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 105 (accept_3_5 8 22 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  105 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 105 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 22 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 105 (accept_3_5 5 22 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 105 (Polychromatic418967fa.accept_20_4_2_5_1_4607 4 22 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 105 (accept_3_5 2 22 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 22
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 105)))))))))))))))))))))) (allB_succ 21
  105 (allA_succ_of_accept 20 21 105 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 21 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 21 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 105 3 6 7 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 105
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 21 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 105 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 21 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 105 3 5 7 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 21 105 7 2 3 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 21 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 21 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 105 3 4 7 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 21 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 21 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 105 3 3 7 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 21 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 105 7 1 3 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 21 105 3 2 7 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 105
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 21 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 105 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 21 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 105 3 1 7 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 105 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 21 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 105
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 21 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 21 105))))))))))))))))))))) (allB_succ 20 105 (allA_succ_of_accept 19 20 105 (accept_3_4 19 20 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 105 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 20 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 20 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 20 105 (accept_3_4 16 20 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 20
  105 5 3 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  20 105 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 20 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 20 105 (accept_3_4 13 20 105 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 20 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 20 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 105 5 2 4 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 105
  (Polychromatic418967fa.accept_19_9_1_10_1_4606 9 20 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 20 105 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 20 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 105 (accept_3_4 7 20 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 20 105 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 20 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 20 105 5 1 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 20 105 (accept_3_4 4 20 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 20 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 105
  (Polychromatic418967fa.accept_25_2_20_5_1_4605 2 20 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 20 105 (accept_3_4 1 20 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  105)))))))))))))))))))) (allB_succ 19 105 (allA_succ_of_accept 18 19 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  19 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 105 (accept_3_5 17 19
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 105 (Polychromatic418967fa.accept_6_4_1_3_1_77
  16 19 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 105
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 19 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 19 105 (accept_3_5 14 19 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  19 105 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 19 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 19 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 19 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 105 (accept_3_5 11 19 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 105
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 19 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 19 105 (accept_3_5 8 19 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19
  105 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 19 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 19 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 105 (accept_3_5 5 19 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 19 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 105 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 19
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 105 (accept_3_5 2 19 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 105 (Polychromatic418967fa.accept_10_1_9_5_1_83 1
  19 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 105))))))))))))))))))) (allB_succ 18
  105 (allA_succ_of_accept 17 18 105 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 18 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 105 (Polychromatic418967fa.accept_12_4_6_9_1_548
  16 18 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 105 3 5 6 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 105
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 18 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 105 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 18 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 105 3 4 6 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 105
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 18 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 18 105 3 3 6 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 18 105 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 18 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 105 3 2 6 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 105
  (Polychromatic418967fa.accept_19_5_18_10_1_4604 5 18 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 18 105 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 18 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 18 105 3 1 6 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 18 105 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 18 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 105
  (Polychromatic418967fa.accept_11_1_7_6_1_378 1 18 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 105)))))))))))))))))) (allB_succ 17 105 (allA_succ_of_accept 16 17 105 (accept_3_4 16 17 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 105 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 17 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 17 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 105 (accept_3_4 13 17 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 17 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 105 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 17 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 105 (accept_3_4 10 17 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 105 (Polychromatic418967fa.accept_18_9_17_15_1_2267 9 17 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 105 (accept_3_4 7 17 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  105 (Polychromatic418967fa.accept_18_6_17_15_1_4603 6 17 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 17 105 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 17 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 105 (accept_3_4 4 17 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 105 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 17 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 105
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 17 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 105 (accept_3_4 1 17 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  105))))))))))))))))) (allB_succ 16 105 (allA_succ_of_accept 15 16 105 (Polychromatic418967fa.accept_13_2_3_1_1_3823 15
  16 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 105 (accept_3_5 14 16
  105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 105 (Polychromatic418967fa.accept_6_1_4_3_1_14
  13 16 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 105
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 16 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 105 (accept_3_5 11 16 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  16 105 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 16 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 16 105 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 16 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 105 (accept_3_5 8 16 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 105
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 16 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 105 (accept_3_5 5 16 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16
  105 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 16 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 16 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 16 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 105 (accept_3_5 2 16 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 16 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 105)))))))))))))))) (allB_succ 15 105 (allA_succ_of_accept 14 15
  105 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 105 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 15 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 105 3 4 5 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 105 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 15 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 105 5 2 3 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 15 105 3 3 5 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 105
  (Polychromatic418967fa.accept_14_8_1_7_1_3725 8 15 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 105 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 15 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 105 3 2 5 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 15 105 5 1 3 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 105 (Polychromatic418967fa.accept_19_4_15_10_1_4602 4 15 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 105 3 1 5 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 105 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 15 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 105))))))))))))))) (allB_succ 14 105 (allA_succ_of_accept 13 14 105
  (accept_3_4 13 14 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 105
  (Polychromatic418967fa.accept_9_3_5_6_1_253 12 14 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 105 (accept_3_4 10 14 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 105 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 14 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 105 (Polychromatic418967fa.accept_9_8_5_6_1_538 8
  14 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 14 105 7 1 2 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 14 105
  (Polychromatic418967fa.accept_10_6_4_5_1_615 6 14 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 14 105 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 14 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 105 (accept_3_4 4 14 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 14 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 105 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  14 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 105 (accept_3_4 1 14 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 105)))))))))))))) (allB_succ 13 105 (allA_succ_of_accept 12 13
  105 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 13 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 105 (accept_3_5 11 13 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 105 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 13 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 105 (Polychromatic418967fa.accept_19_9_13_10_1_4601 9 13 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 105 (accept_3_5 8 13 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 105 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 13 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 105
  (Polychromatic418967fa.accept_14_6_13_7_1_2015 6 13 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 105 (accept_3_5 5 13 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  105 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 105 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 13 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 105 (accept_3_5 2 13 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 105 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 13 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 105))))))))))))) (allB_succ 12 105 (allA_succ_of_accept 11 12
  105 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 12 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 12 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 105 3 3 4 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 105 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 12 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 105
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 12 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 105 3 2 4 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 105 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 12 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 105 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 12 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 12 105 3 1 4 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 12 105
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 12 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 12 105 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 12 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 105)))))))))))) (allB_succ 11 105 (allA_succ_of_accept 10 11 105
  (accept_3_4 10 11 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 105
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 11 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 105 (accept_3_4 7 11 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 105 (Polychromatic418967fa.accept_9_5_2_6_1_265 5
  11 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 105 (accept_3_4 4 11 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 105 (Polychromatic418967fa.accept_9_3_2_6_1_264 3
  11 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 105 (accept_3_4 1 11 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  105))))))))))) (allB_succ 10 105 (allA_succ_of_accept 9 10 105 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 10 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 105 (accept_3_5 8 10 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 105
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 10 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 10 105 5 1 2 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 10 105 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 10 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 105 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 105 (accept_3_5 2 10 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 105 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 10
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 105)))))))))) (allB_succ 9 105
  (allA_succ_of_accept 8 9 105 (Polychromatic418967fa.accept_13_8_9_1_1_2147 8 9 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 105 (Polychromatic418967fa.accept_19_7_9_10_1_4600 7 9 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 105 3 2 3 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 105
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 9 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 105 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 9 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 105 3 1 3 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 105 (Polychromatic418967fa.accept_13_2_9_1_1_67 2 9 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 105
  (Polychromatic418967fa.accept_10_1_9_5_1_83 1 9 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 105))))))))) (allB_succ 8 105 (allA_succ_of_accept 7 8 105 (accept_3_4 7 8 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 105 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 8 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 105
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 105 (accept_3_4 4 8 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 105
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 8 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 105 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 8 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 105 (accept_3_4 1 8 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 105)))))))) (allB_succ 7 105 (allA_succ_of_accept 6 7 105
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 105 (accept_3_5 5 7 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 105
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 105 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 7 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 105 (accept_3_5 2 7 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 105 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 7 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 105))))))) (allB_succ 6 105 (allA_succ_of_accept 5 6 105
  (Polychromatic418967fa.accept_13_5_6_1_1_822 5 6 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 105 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 6 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 105 3 1 2 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 105 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 6 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 105
  (Polychromatic418967fa.accept_10_1_6_5_1_304 1 6 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 105)))))) (allB_succ 5 105 (allA_succ_of_accept 4 5 105 (accept_3_4 4 5 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 105 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 5 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 105 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 5
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 105 (accept_3_4 1 5 105
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 105))))) (allB_succ 4 105 (allA_succ_of_accept 3 4 105
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 4 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 105 (accept_3_5 2 4 105 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 105
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 105)))) (allB_succ 3 105 (allA_succ_of_accept 2 3 105 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 105
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 3 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 105))) (allB_succ 2 105 (allA_succ_of_accept 1 2 105 (accept_3_4 1 2 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 105)) (allB_two
  105)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


