-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch78
-- name    : Polychromatic418967fa_Branch78
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:08:59.755932+00:00
-- url     : https://prove2.me/theorems/aab95b3e-36d0-4eb1-8c7a-5ac24b8c80be
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

def Polychromatic418967fa.branch_78 : allB 78 78 :=
  allB_succ' 2 77 78 (Eq.refl Bool.true) (allA_succ_of_accept 1 77 78 (accept_3_4 1 77 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 78)) (allB_succ' 3 76 78 (Eq.refl Bool.true) (allA_succ_of_gcd 2 76 78 2 1 38 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 78
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 76 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 78))) (allB_succ' 4 75 78 (Eq.refl Bool.true) (allA_succ_of_gcd 3 75 78 3 1 25 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 78
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 75 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 75 78)))) (allB_succ' 5 74 78 (Eq.refl Bool.true) (allA_succ_of_gcd 4 74 78 2 2 37 39
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 78
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 74 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 78 2 1 37 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 78 (accept_3_4 1 74 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74 78)))))
  (allB_succ' 6 73 78 (Eq.refl Bool.true) (allA_succ_of_accept 5 73 78 (accept_3_5 5 73 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 78 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 73 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 78 (accept_3_5 2 73 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 78 (Polychromatic418967fa.accept_10_1_3_8_1_136 1
  73 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 78)))))) (allB_succ' 7 72 78 (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 72 78 6 1 12 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 72 78 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 72 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 78 2 2 36 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 72 78 3 1 24 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 72 78 2 1 36 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 78 (Polychromatic418967fa.accept_14_1_2_8_1_655 1 72
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72 78))))))) (allB_succ' 8 71 78 (Eq.refl
  Bool.true) (allA_succ_of_accept 7 71 78 (accept_3_4 7 71 78 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 71 78 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 71 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 78 (accept_3_4 4 71 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71 78 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 71 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 78
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 71 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 71 78 (accept_3_4 1 71 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71 78))))))))
  (allB_succ' 9 70 78 (Eq.refl Bool.true) (allA_succ_of_gcd 8 70 78 2 4 35 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 70 78 (Polychromatic418967fa.accept_15_7_10_3_1_2891 7
  70 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 78 2 3 35 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 78 (accept_3_5 5 70
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 78 2 2 35 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 70 78
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 70 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 70 78 2 1 35 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 70 78 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 70 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 70 78))))))))) (allB_succ' 10 69 78 (Eq.refl Bool.true) (allA_succ_of_gcd 9
  69 78 3 3 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8
  69 78 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 69 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 69 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 78 3 2 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 78 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 69
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 78
  (Polychromatic418967fa.accept_10_4_9_8_1_125 4 69 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 69 78 3 1 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 69 78 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 69 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 78 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 69 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69 78)))))))))) (allB_succ' 11 68 78 (Eq.refl
  Bool.true) (allA_succ_of_gcd 10 68 78 2 5 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 68 78 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 68 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 78 2 4 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 78 (accept_3_4 7 68 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 68 78 2 3 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 68 78 (Polychromatic418967fa.accept_15_5_8_3_1_556 5 68 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 78 2 2 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 78 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 68
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 78 2 1 34 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 78 (accept_3_4 1 68
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68 78))))))))))) (allB_succ' 12 67 78 (Eq.refl Bool.true)
  (allA_succ_of_accept 11 67 78 (accept_3_5 11 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 67
  78 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 67 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 78 (accept_3_5 8 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 67 78 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 67 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 78 (Polychromatic418967fa.accept_17_6_16_10_1_2890 6 67 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 78 (accept_3_5 5 67 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67 78 (Polychromatic418967fa.accept_14_4_11_8_1_2034 4 67 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 78
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 67 78 (accept_3_5 2 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 67 78)))))))))))) (allB_succ' 13 66 78 (Eq.refl Bool.true) (allA_succ_of_gcd 12 66 78 6 2 11 13 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 78
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 66 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 78 2 5 33 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 66 78 3 3 22 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 66 78 2 4 33 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 78 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 66 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 78 6 1 11 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 78 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 66 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 78 2 2 33 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 66 78 3 1 22 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 66 78 2 1 33 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 78
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 66 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 78))))))))))))) (allB_succ' 14 65 78 (Eq.refl Bool.true) (allA_succ_of_gcd 13 65 78 13 1 5 6 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 65 78
  (Polychromatic418967fa.accept_9_3_2_6_1_264 12 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 65 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 78 (accept_3_4 10 65 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 65 78 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 65 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 78 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 65
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 78 (accept_3_4 7 65 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 78 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 65
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 78
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 78 (accept_3_4 4 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 78
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 78 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 65 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 78 (accept_3_4 1 65 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 78)))))))))))))) (allB_succ' 15 64 78 (Eq.refl Bool.true) (allA_succ_of_gcd 14 64 78 2 7 32
  39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 78
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 64 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 64 78 2 6 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 64 78 (accept_3_5 11 64 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 78
  2 5 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 64 78
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 64 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 64 78 2 4 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 64 78 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 64 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 78 2 3 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 78 (accept_3_5 5 64 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 64 78 2 2 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 64 78 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 64 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 78 2 1 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 78 (Polychromatic418967fa.accept_15_1_4_3_1_1928 1
  64 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64 78))))))))))))))) (allB_succ' 16 63 78
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 63 78 3 5 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 63 78 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 63 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 63 78 3 4 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 63 78 (Polychromatic418967fa.accept_10_1_3_8_1_136 11 63 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 78 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 63 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 78 3 3 21 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 78
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 63 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 78 (Polychromatic418967fa.accept_16_7_15_14_1_2889 7 63 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 78 3 2 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 78
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 63 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 63 78 3 1 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 63 78 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 63 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 78)))))))))))))))) (allB_succ' 17 62 78
  (Eq.refl Bool.true) (allA_succ_of_gcd 16 62 78 2 8 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 62 78 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 62 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 78 2 7 31 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 78 (accept_3_4 13 62 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 78 2 6 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 78 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 62 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 62 78 2 5 31 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 62 78
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 62 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 62 78 2 4 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 62 78 (accept_3_4 7 62 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 78 2
  3 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 62 78
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 62 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 62 78 2 2 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 62 78 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 62 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 78 2 1 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 78 (accept_3_4 1 62 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 78))))))))))))))))) (allB_succ' 18 61 78 (Eq.refl Bool.true) (allA_succ_of_accept 17 61 78
  (accept_3_5 17 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 61 78
  (Polychromatic418967fa.accept_11_5_6_1_1_988 16 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 61 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 78 (accept_3_5 14 61 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 61 78 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 61 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 78 (Polychromatic418967fa.accept_9_3_7_6_1_76 12
  61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 61 78 (accept_3_5 11 61 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 61 78 (Polychromatic418967fa.accept_7_3_5_1_1_72 10
  61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 78
  (Polychromatic418967fa.accept_10_9_1_8_1_755 9 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 61 78 (accept_3_5 8 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 78
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 61 78 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 61 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 78 (accept_3_5 5 61 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 61 78 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 61 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 78 (accept_3_5 2 61 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 78 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 61
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 78)))))))))))))))))) (allB_succ' 19 60 78
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 60 78 6 3 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 60 78 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 60 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 78 2 8 30 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 78 3 5 20 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 78 2 7 30 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 78
  (Polychromatic418967fa.accept_17_13_9_10_1_2888 13 60 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 78 6 2 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 78 (Polychromatic418967fa.accept_14_11_4_8_1_664 11 60 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 78 2 5 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 78 3 3 20 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 60 78 2 4 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 78 (Polychromatic418967fa.accept_21_7_18_15_1_2887 7 60 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 78 6 1 10 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 78
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 60 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 60 78 2 2 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 60 78 3 1 20 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 60 78 2 1 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 78 (Polychromatic418967fa.accept_17_1_9_10_1_1864 1 60 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 78))))))))))))))))))) (allB_succ' 20 59 78 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 59 78 (accept_3_4 19 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59
  78 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 59 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 78 (accept_3_4 16 59 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 59 78 (Polychromatic418967fa.accept_17_15_8_10_1_2886 15 59 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 78 (Polychromatic418967fa.accept_10_4_9_8_1_125 14
  59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 78 (accept_3_4 13 59 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 78 (Polychromatic418967fa.accept_7_5_3_1_1_424 12
  59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 78
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 78 (accept_3_4 10 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 59
  78 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 78 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 59 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 78 (accept_3_4 7 59 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 78 (Polychromatic418967fa.accept_21_6_17_15_1_2833 6 59 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 78 (accept_3_4 4 59 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 78 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 59
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 78
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 78 (accept_3_4 1 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  78)))))))))))))))))))) (allB_succ' 21 58 78 (Eq.refl Bool.true) (allA_succ_of_gcd 20 58 78 2 10 29 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 78
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 58 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 58 78 2 9 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 58 78 (accept_3_5 17 58 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58 78
  2 8 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 58
  78 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 58 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 58 78 2 7 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 58 78 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 58 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 78 2 6 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 78 (accept_3_5 11 58 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 58 78 2 5 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 58 78 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 58 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 58 78 2 4 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 58 78 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 58
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 78 2 3 29 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 78 (accept_3_5 5 58
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 78 2 2 29 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 58 78
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 58 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 58 78 2 1 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 58 78 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 58 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 58 78))))))))))))))))))))) (allB_succ' 22 57 78 (Eq.refl Bool.true) (allA_succ_of_gcd
  21 57 78 3 7 19 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 57 78 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 57 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 78 3 6 19 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 78
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 57 78 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 57 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 57 78 3 5 19 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 57 78 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 57 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 78
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 57 78 3 4 19 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 57 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 78 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 57 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 78 3 3 19 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 78
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 78 3 2 19 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 78 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 57 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 78
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 57 78 3 1 19 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 57 78 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 57 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 78 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 57 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 78)))))))))))))))))))))) (allB_succ' 23 56
  78 (Eq.refl Bool.true) (allA_succ_of_gcd 22 56 78 2 11 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 78 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 56 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 56 78 2 10 28 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 78 (accept_3_4 19 56 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 78 2 9 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 56 78 (Polychromatic418967fa.accept_9_8_2_6_1_875 17
  56 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 78 2 8 28 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 78
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 56 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 56 78 2 7 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 56 78 (accept_3_4 13 56 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 78
  2 6 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56
  78 (Polychromatic418967fa.accept_20_11_16_18_1_2885 11 56 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 56 78 2 5 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 56 78 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 56 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 78 2 4 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 78 (accept_3_4 7 56 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 56 78 2 3 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 56 78 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 56 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 78 2 2 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 78 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 56
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 78 2 1 28 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 78 (accept_3_4 1 56
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 78))))))))))))))))))))))) (allB_succ' 24 55 78 (Eq.refl
  Bool.true) (allA_succ_of_accept 23 55 78 (accept_3_5 23 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 55 78 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 55 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 78 (accept_3_5 20 55 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 78 (Polychromatic418967fa.accept_7_5_6_1_1_407 19
  55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 78
  (Polychromatic418967fa.accept_21_18_13_15_1_2884 18 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 78 (accept_3_5 17 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 55
  78 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 55 78 (Polychromatic418967fa.accept_16_15_7_14_1_2883 15 55 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 78 (accept_3_5 14 55 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 55 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 78 (Polychromatic418967fa.accept_7_5_6_1_1_407 12
  55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 78 (accept_3_5 11 55 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 78 (Polychromatic418967fa.accept_16_10_7_14_1_2882
  10 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 78 (accept_3_5 8 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 78
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 78 (Polychromatic418967fa.accept_15_6_10_3_1_2844 6 55 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 78 (accept_3_5 5 55 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 78 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 55 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 78 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 55
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 78 (accept_3_5 2 55 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 78)))))))))))))))))))))))) (allB_succ' 25
  54 78 (Eq.refl Bool.true) (allA_succ_of_gcd 24 54 78 6 4 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 78 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 54 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 78 2 11 27 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 54 78 3 7 18 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 54 78 2 10 27 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 78
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 54 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 78 6 3 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 78 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 54 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 78 2 8 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 54 78 3 5 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 54 78 2 7 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 78 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 54 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 78 6 2 9 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 78
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 54 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 54 78 2 5 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 54 78 3 3 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 54 78 2 4 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 54 78 (Polychromatic418967fa.accept_17_7_3_10_1_2881 7 54 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 78 6 1 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 78 (Polychromatic418967fa.accept_15_5_9_3_1_528 5 54 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 78 2 2 27 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 54 78 3 1 18 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 54 78 2 1 27 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 78
  (Polychromatic418967fa.accept_21_1_12_15_1_2880 1 54 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 78))))))))))))))))))))))))) (allB_succ' 26 53 78 (Eq.refl Bool.true) (allA_succ_of_accept 25 53 78
  (accept_3_4 25 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 78
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 53 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 78 (accept_3_4 22 53 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 53 78 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 53 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 78 (Polychromatic418967fa.accept_9_2_8_6_1_79 20
  53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 78 (accept_3_4 19 53 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 78 (Polychromatic418967fa.accept_14_4_11_8_1_2034
  18 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 78
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 78 (accept_3_4 16 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53
  78 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 53 78 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 53 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 78 (accept_3_4 13 53 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 53 78 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 53 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 78 (accept_3_4 10 53 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 78 (Polychromatic418967fa.accept_15_9_8_3_1_557 9
  53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 78
  (Polychromatic418967fa.accept_17_8_2_10_1_2879 8 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 78 (accept_3_4 7 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 78
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 78 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 53 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 78 (accept_3_4 4 53 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 78 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 53
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 78 (accept_3_4 1 53 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 78)))))))))))))))))))))))))) (allB_succ' 27 52 78 (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 52 78 26 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 52 78 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 52 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 78 2 12 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 78 (accept_3_5 23 52 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 78 2 11 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 52 78 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 52 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 78 2 10 26 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 78
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 52 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 78 2 9 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 78 (accept_3_5 17 52 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 78
  2 8 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 52
  78 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 52 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 52 78 2 7 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 13 52 78 13 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 52 78 2 6 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 52 78 (accept_3_5 11 52 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 78
  2 5 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 52 78
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 52 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 52 78 2 4 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 52 78 (Polychromatic418967fa.accept_16_7_4_14_1_2860 7 52 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 78 2 3 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 78 (accept_3_5 5 52 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 52 78 2 2 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 52 78 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 52 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 78 2 1 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 78 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 52
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 78))))))))))))))))))))))))))) (allB_succ'
  28 51 78 (Eq.refl Bool.true) (allA_succ_of_gcd 27 51 78 3 9 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 78 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 51 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 51 78 3 8 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 51 78 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 51 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 78 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 51 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 78 3 7 17 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 78
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 78 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 51 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 78 3 6 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 78
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 51 78 3 5 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 51 78 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 51 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 78 3 4 17 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 78
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 78 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 51 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 78 3 3 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 78 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 51 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 78
  (Polychromatic418967fa.accept_19_7_13_2_1_2878 7 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 51 78 3 2 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 51 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 78 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 51 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 78 3 1 17 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 78
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 51 78)))))))))))))))))))))))))))) (allB_succ' 29 50 78 (Eq.refl Bool.true)
  (allA_succ_of_gcd 28 50 78 2 14 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 50 78 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 50 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 78 2 13 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 78 (accept_3_4 25 50 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 50 78 2 12 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 50 78 (Polychromatic418967fa.accept_15_8_5_3_1_1990 23 50 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 78 2 11 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 78 (Polychromatic418967fa.accept_9_3_5_6_1_253 21
  50 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 78 2 10 25 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 78 (accept_3_4 19 50
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 78 2 9 25 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 50 78
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 50 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 50 78 2 8 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 50 78 (Polychromatic418967fa.accept_12_3_2_6_1_138 15 50 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 78 2 7 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 78 (accept_3_4 13 50 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 50 78 2 6 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 50 78 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 50 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 78 2 5 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 78 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 50
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 78 2 4 25 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 78 (accept_3_4 7 50
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 78 2 3 25 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 50 78
  (Polychromatic418967fa.accept_11_5_6_1_1_988 5 50 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 50 78 2 2 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 50 78 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 50 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 78 2 1 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 78 (accept_3_4 1 50 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 78))))))))))))))))))))))))))))) (allB_succ' 30 49 78 (Eq.refl Bool.true) (allA_succ_of_accept
  29 49 78 (accept_3_5 29 49 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 78
  (Polychromatic418967fa.accept_9_1_4_6_1_5 28 49 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 49 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 78 (accept_3_5 26 49 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 49 78 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 49 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 78 (Polychromatic418967fa.accept_10_4_9_8_1_125 24
  49 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 78 (accept_3_5 23 49 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 78 (Polychromatic418967fa.accept_15_7_4_3_1_1930
  22 49 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 78
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 49 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 78 (accept_3_5 20 49 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49
  78 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 49 78 (Polychromatic418967fa.accept_21_18_7_15_1_2877 18 49 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 78 (accept_3_5 17 49 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 49 78 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 49 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  49 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 78 (accept_3_5 14 49 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 78 (Polychromatic418967fa.accept_14_13_7_8_1_677
  13 49 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 78
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 49 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 78 (accept_3_5 11 49 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49
  78 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 49 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 49 78 (Polychromatic418967fa.accept_18_9_13_6_1_877 9 49 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 78 (accept_3_5 8 49 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 49 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 78 (Polychromatic418967fa.accept_11_6_5_1_1_586 6
  49 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 78 (accept_3_5 5 49 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 78 (Polychromatic418967fa.accept_10_4_9_8_1_125 4
  49 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 78
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 78 (accept_3_5 2 49 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 78
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 49 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 49 78)))))))))))))))))))))))))))))) (allB_succ' 31 48 78 (Eq.refl Bool.true) (allA_succ_of_gcd 30 48 78 6 5
  8 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 78
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 48 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 48 78 2 14 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 48 78 3 9 16 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 48 78 2 13 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 48 78 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 48 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 78 6 4 8 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 78 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 48 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 78 2 11 24 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 48 78 3 7 16 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 48 78 2 10 24 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 78
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 48 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 78 6 3 8 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 78 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 48 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 78 2 8 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 48 78 3 5 16 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 48 78 2 7 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 78 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 48 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 78 6 2 8 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 78
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 48 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 48 78 2 5 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 48 78 3 3 16 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 48 78 2 4 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 78 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 48 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 78 6 1 8 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 78 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 48 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 78 2 2 24 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 48 78 3 1 16 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 48 78 2 1 24 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 78
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 48 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 78))))))))))))))))))))))))))))))) (allB_succ' 32 47 78 (Eq.refl Bool.true) (allA_succ_of_accept 31 47 78
  (accept_3_4 31 47 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 78
  (Polychromatic418967fa.accept_9_3_2_6_1_264 30 47 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 47 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 78 (accept_3_4 28 47 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 47 78 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 47 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 78 (Polychromatic418967fa.accept_9_8_2_6_1_875 26
  47 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 78 (accept_3_4 25 47 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 78 (Polychromatic418967fa.accept_7_3_5_1_1_72 24
  47 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 78
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 47 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 78 (accept_3_4 22 47 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47
  78 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 78 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 47 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 78 (accept_3_4 19 47 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 78 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 47 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 78 (accept_3_4 16 47 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 78 (Polychromatic418967fa.accept_10_5_7_8_1_1176
  15 47 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 78
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 47 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 78 (accept_3_4 13 47 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47
  78 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 47 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 47 78 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 47 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 78 (accept_3_4 10 47 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 47 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 78 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 47
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 78 (accept_3_4 7 47 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 78 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 47
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 78 (accept_3_4 4 47 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 78
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 47 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 78 (Polychromatic418967fa.accept_11_2_3_1_1_244 2 47 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 78 (accept_3_4 1 47 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 78)))))))))))))))))))))))))))))))) (allB_succ' 33 46 78 (Eq.refl Bool.true) (allA_succ_of_gcd
  32 46 78 2 16 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 46 78 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 46 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 78 2 15 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 78 (accept_3_5 29 46 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 46 78 2 14 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 46 78 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 46 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 78 2 13 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 78 (Polychromatic418967fa.accept_9_7_1_6_1_261 25
  46 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 78 2 12 23 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 78 (accept_3_5 23 46
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 78 2 11 23 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 78
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 46 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 46 78 2 10 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 46 78 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 46 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 78 2 9 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 78 (accept_3_5 17 46 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 46 78 2 8 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 46 78 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 46 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 78 2 7 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 78 (Polychromatic418967fa.accept_9_4_1_6_1_284 13
  46 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 78 2 6 23 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 78 (accept_3_5 11 46
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 78 2 5 23 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 78
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 46 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 78 2 4 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 78 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 46 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 78 2 3 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 78 (accept_3_5 5 46 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 78 2 2 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 78 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 46 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 78 2 1 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 78 (Polychromatic418967fa.accept_19_1_8_2_1_2876 1
  46 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46 78)))))))))))))))))))))))))))))))))
  (allB_succ' 34 45 78 (Eq.refl Bool.true) (allA_succ_of_gcd 33 45 78 3 11 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 78 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 45
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 78
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 78 3 10 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 78 (Polychromatic418967fa.accept_21_8_3_15_1_2875 29 45 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 78 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 45 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 78 3 9 15 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 78
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 45 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 78 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 45 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 78 3 8 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 78
  (Polychromatic418967fa.accept_10_2_5_8_1_139 22 45 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 78 3 7 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 78 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 45 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 78 3 6 15 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 78
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 45 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 78 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 45 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 78 3 5 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 78 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 45 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 78
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 45 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 78 3 4 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 78 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 45 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 78 3 3 15 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 78
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 45 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 78 3 2 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 78 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 45 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 78
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 45 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 78 3 1 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 78 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 45 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 78 (Polychromatic418967fa.accept_16_1_13_14_1_1064 1 45 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 78))))))))))))))))))))))))))))))))))
  (allB_succ' 35 44 78 (Eq.refl Bool.true) (allA_succ_of_gcd 34 44 78 2 17 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 78 (Polychromatic418967fa.accept_12_9_8_6_1_466 33
  44 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 44 78 2 16 22 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 78 (accept_3_4 31 44
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 78 2 15 22 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44 78
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 44 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 44 78 2 14 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 44 78 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 44 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 78 2 13 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 78 (accept_3_4 25 44 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 44 78 2 12 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 44 78 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 44 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 78 2 11 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 78 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 44
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 78 2 10 22 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 78 (accept_3_4 19 44
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 78 2 9 22 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 44 78
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 44 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 44 78 2 8 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 44 78 (Polychromatic418967fa.accept_12_3_8_6_1_895 15 44 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 78 2 7 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 78 (accept_3_4 13 44 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 44 78 2 6 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 44 78 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 44 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 78 2 5 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 78 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 44
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 78 2 4 22 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 78 (accept_3_4 7 44
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 78 2 3 22 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44 78
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 44 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 44 78 2 2 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 44 78 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 44 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 78 2 1 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 78 (accept_3_4 1 44 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 78))))))))))))))))))))))))))))))))))) (allB_succ' 36 43 78 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 43 78 (accept_3_5 35 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43
  78 (Polychromatic418967fa.accept_23_11_20_9_1_2874 34 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 78 (accept_3_5 32 43 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 78 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 43 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 78
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 78 (accept_3_5 29 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 43
  78 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 43 78 (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 43 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 78 (accept_3_5 26 43 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 43 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 78 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  24 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 78 (accept_3_5 23 43
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 78 (Polychromatic418967fa.accept_9_4_7_6_1_255
  22 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 78 (accept_3_5 20 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43
  78 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 43 78 (Polychromatic418967fa.accept_17_1_9_10_1_1864 18 43 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 78 (accept_3_5 17 43 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 43 78 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 43 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 78 (Polychromatic418967fa.accept_10_5_3_8_1_1165
  15 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 78 (accept_3_5 14 43
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 13
  43 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 78
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 78 (accept_3_5 11 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 43
  78 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 43 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 78 (accept_3_5 8 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 43 78 (Polychromatic418967fa.accept_14_7_1_8_1_2873 7 43 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 78 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 43 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 78 (accept_3_5 5 43 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 78 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 43 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 78
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 43 78 (accept_3_5 2 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 43 78)))))))))))))))))))))))))))))))))))) (allB_succ' 37 42 78 (Eq.refl Bool.true) (allA_succ_of_gcd 36 42
  78 6 6 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42
  78 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 42 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 42 78 2 17 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 42 78 3 11 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 42 78 2 16 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 78 (Polychromatic418967fa.accept_16_15_10_14_1_2872 31 42 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 78 6 5 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 78 (Polychromatic418967fa.accept_16_13_10_14_1_2871 29 42 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 78 2 14 21 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 78 3 9 14 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 42 78 2 13 21 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 78
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 42 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 78 6 4 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 78 (Polychromatic418967fa.accept_15_8_12_3_1_1912 23 42 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 78 2 11 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 78 3 7 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 78 2 10 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 78 (Polychromatic418967fa.accept_17_2_8_10_1_2870 19 42 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 78 6 3 7 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 78
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 42 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 78 2 8 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 42 78 3 5 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 42 78 2 7 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 78 (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 42 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 78 6 2 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 78 (Polychromatic418967fa.accept_19_11_4_2_1_1700 11 42 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 78 2 5 21 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 42 78 3 3 14 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 42 78 2 4 21 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 78
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 42 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 78 6 1 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 78 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 42 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 78 2 2 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 42 78 3 1 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 42 78 2 1 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 78 (Polychromatic418967fa.accept_22_1_20_12_1_2869 1 42 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 78)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 41 78 (Eq.refl Bool.true) (allA_succ_of_accept 37 41 78 (accept_3_4 37 41 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 78 (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 41 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 78
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 41 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 78 (accept_3_4 34 41 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41
  78 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 41 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 78 (Polychromatic418967fa.accept_24_8_17_6_1_2868 32 41 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 78 (accept_3_4 31 41 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 78 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 41 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 78 (Polychromatic418967fa.accept_9_2_5_6_1_536 29
  41 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 78 (accept_3_4 28 41 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  41 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 78
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 41 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 78 (accept_3_4 25 41 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41
  78 (Polychromatic418967fa.accept_19_5_3_2_1_2867 24 41 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 41 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 78 (accept_3_4 22 41 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 41 78 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 41 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 78 (Polychromatic418967fa.accept_9_2_5_6_1_536 20
  41 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 78 (accept_3_4 19 41 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 78 (Polychromatic418967fa.accept_17_1_7_10_1_1835
  18 41 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 78
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 41 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 78 (accept_3_4 16 41 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41
  78 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 41 78 (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 41 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 78 (accept_3_4 13 41 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 41 78 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 41 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  41 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 78 (accept_3_4 10 41 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 78 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 41
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 78
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 41 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 78 (accept_3_4 7 41 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 78
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 6 41 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 78 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 41 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 78 (accept_3_4 4 41 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 78 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 41
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 78 (accept_3_4 1 41 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 78)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 40 78
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 40 78 2 19 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 40 78 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 40 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 78 2 18 20 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 78 (accept_3_5 35 40 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 78 2 17 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 78 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 40 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 78 2 16 20 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 78
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 40 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 78 2 15 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 78 (accept_3_5 29 40 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40 78
  2 14 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 40
  78 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 40 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 40 78 2 13 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 40 78 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 40 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 78 2 12 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 78 (accept_3_5 23 40 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 40 78 2 11 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 40 78 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 40 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 78 2 10 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 78 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 40
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 78 2 9 20 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 78 (accept_3_5 17 40
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 78 2 8 20 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 40 78
  (Polychromatic418967fa.accept_12_3_4_6_1_434 15 40 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 40 78 2 7 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 40 78 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 40 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 78 2 6 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 78 (accept_3_5 11 40 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 40 78 2 5 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 40 78 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 40 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 40 78 2 4 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 40 78 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 40
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 78 2 3 20 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 78 (accept_3_5 5 40
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 78 2 2 20 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 40 78
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 40 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 40 78 2 1 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 40 78 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 40 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 40 78))))))))))))))))))))))))))))))))))))))) (allB_succ 39 78 (allA_succ_of_accept 38
  39 78 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 39 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 39 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 78 3 12 13 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 78 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 39 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 78
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 39 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 78 3 11 13 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 78 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 39 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 78 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 39 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 78 3 10 13 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 78 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 39 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 78 3 9 13 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 39 78 13 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 39 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 39 78 3 8 13 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 39 78
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 39 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 39 78 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 39 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 78 3 7 13 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 78 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 39 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 78
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 39 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 39 78 3 6 13 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 39 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 78 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 39 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 39 78 3 5 13 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 39 78
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 39 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 39 78 13 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 39 78 3 4 13 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 39 78 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 39 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 78 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 39 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 78 3 3 13 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 78
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 39 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 78 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 39 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 39 78 3 2 13 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 39 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 78
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 39 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 39 78 3 1 13 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 39 78 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 39 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 78)))))))))))))))))))))))))))))))))))))))
  (allB_succ 38 78 (allA_succ_of_accept 37 38 78 (accept_3_4 37 38 78 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 38 78 2 18 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 38 78 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 38 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 38 78 2 17 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 38 78 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 38 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 78 2 16 19 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 78 (accept_3_4 31 38 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 78 2 15 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 78 (Polychromatic418967fa.accept_21_8_17_15_1_2834
  29 38 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 38 78 2 14 19 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 38 78
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 38 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 38 78 2 13 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 38 78 (accept_3_4 25 38 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 78
  2 12 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38
  78 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 38 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 38 78 2 11 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 38 78 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 38 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 38 78 2 10 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 38 78 (accept_3_4 19 38 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 38 78 2 9 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 38 78 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 38 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 78 2 8 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 78 (Polychromatic418967fa.accept_12_3_2_6_1_138 15
  38 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 78 2 7 19 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 78 (accept_3_4 13 38
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 78 2 6 19 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 78
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 38 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 38 78 2 5 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 38 78 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 38 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 78 2 4 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 78 (accept_3_4 7 38 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 38 78 2 3 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 38 78 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 38 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 78 2 2 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 78 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 38
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 78 2 1 19 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 78 (accept_3_4 1 38
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 78)))))))))))))))))))))))))))))))))))))) (allB_succ 37 78
  (allA_succ_of_accept 36 37 78 (Polychromatic418967fa.accept_22_14_15_12_1_2866 36 37 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 78 (accept_3_5 35 37 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 78 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 37 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 78
  (Polychromatic418967fa.accept_22_11_15_12_1_2865 33 37 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 78 (accept_3_5 32 37 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37
  78 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 78 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 37 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 78 (accept_3_5 29 37 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 78 (Polychromatic418967fa.accept_17_11_3_10_1_2838 28 37 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  37 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 78 (accept_3_5 26 37 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 78 (Polychromatic418967fa.accept_9_7_1_6_1_261 25
  37 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 78
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 37 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 78 (accept_3_5 23 37 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 37
  78 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 37 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 37 78 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 37 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 78 (accept_3_5 20 37 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 37 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 78
  (Polychromatic418967fa.accept_21_18_16_15_1_2864 18 37 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 78 (accept_3_5 17 37 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 37
  78 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 37 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 37 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 78 (accept_3_5 14 37 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 37 78 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 37 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 78 (Polychromatic418967fa.accept_9_3_1_6_1_86 12
  37 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 78 (accept_3_5 11 37 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 78 (Polychromatic418967fa.accept_7_3_2_1_1_225 10
  37 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 78
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 37 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 78 (accept_3_5 8 37 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 78
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 78 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 37 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 78 (accept_3_5 5 37 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 78 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 37 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 78 (accept_3_5 2 37 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 78 (Polychromatic418967fa.accept_14_1_9_8_1_2863 1
  37 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37
  78))))))))))))))))))))))))))))))))))))) (allB_succ 36 78 (allA_succ_of_accept 35 36 78
  (Polychromatic418967fa.accept_11_2_3_1_1_244 35 36 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 78 2 17 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 36 78 3 11 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 36 78 2 16 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 36 78 (Polychromatic418967fa.accept_15_1_6_3_1_2827 31 36 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 78 6 5 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 78 (Polychromatic418967fa.accept_17_12_2_10_1_2862 29 36 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 78 2 14 18 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 36 78 3 9 12 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 36 78 2 13 18 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 78
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 36 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 78 6 4 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 78 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 36 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 78 2 11 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 36 78 3 7 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 36 78 2 10 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 78 (Polychromatic418967fa.accept_23_19_13_9_1_2861 19 36 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 78 6 3 6 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 78
  (Polychromatic418967fa.accept_16_1_4_14_1_1896 17 36 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 36 78 2 8 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 36 78 3 5 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 36 78 2 7 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 78 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 36 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 78 6 2 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 78 (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 36 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 78 2 5 18 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 36 78 3 3 12 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 36 78 2 4 18 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 78
  (Polychromatic418967fa.accept_16_7_4_14_1_2860 7 36 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 78 6 1 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 78 (Polychromatic418967fa.accept_15_5_6_3_1_525 5 36 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 78 2 2 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 36 78 3 1 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 36 78 2 1 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 78 (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 36 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 78))))))))))))))))))))))))))))))))))))
  (allB_succ 35 78 (allA_succ_of_accept 34 35 78 (accept_3_4 34 35 78 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 35 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 35 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 78 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 35 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 78 (accept_3_4 31 35 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 78 (Polychromatic418967fa.accept_9_3_8_6_1_80 30
  35 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 78 (accept_3_4 28 35 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35
  78 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 35 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 78 (Polychromatic418967fa.accept_17_9_1_10_1_2859 26 35 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 78 (accept_3_4 25 35 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 78 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 35 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 78 (Polychromatic418967fa.accept_9_5_8_6_1_281 23
  35 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 78 (accept_3_4 22 35 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 35
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 78
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 35 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 78 (accept_3_4 19 35 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35
  78 (Polychromatic418967fa.accept_19_18_16_2_1_2858 18 35 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 78 (accept_3_4 16 35 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 78 (Polychromatic418967fa.accept_14_1_7_8_1_2063 15 35 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 78
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 35 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 78 (accept_3_4 13 35 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35
  78 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 35 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 35 78 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 35 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 78 (accept_3_4 10 35 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 35 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 78 (Polychromatic418967fa.accept_15_8_5_3_1_1990 8
  35 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 78 (accept_3_4 7 35 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 78 (Polychromatic418967fa.accept_14_6_7_8_1_624 6
  35 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 78 (accept_3_4 4 35 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 78
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 35 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 78 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 35 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 78 (accept_3_4 1 35 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 78))))))))))))))))))))))))))))))))))) (allB_succ 34 78 (allA_succ_of_accept 33 34 78
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 34 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 78 2 16 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 78 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 34 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 78 2 15 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 78 (accept_3_5 29 34 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 34 78 2 14 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 34 78 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 34 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 78 2 13 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 78 (Polychromatic418967fa.accept_19_6_15_2_1_2857
  25 34 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 34 78 2 12 17 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 34 78 (accept_3_5 23 34
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 78 2 11 17 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34 78
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 34 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 34 78 2 10 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 34 78 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 34 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 78 2 9 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 78 (accept_3_5 17 34 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 34 78 2 8 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 34 78 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 34 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 78 2 7 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 78 (Polychromatic418967fa.accept_9_4_7_6_1_255 13
  34 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 78 2 6 17 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 78 (accept_3_5 11 34
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 78 2 5 17 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 78
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 34 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 78 2 4 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 78 (Polychromatic418967fa.accept_14_7_6_8_1_2856 7 34 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 78 2 3 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 78 (accept_3_5 5 34 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 78 2 2 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 78 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 34 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 78 2 1 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 78 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 34
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 78))))))))))))))))))))))))))))))))))
  (allB_succ 33 78 (allA_succ_of_accept 32 33 78 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 33 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 78
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 33 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 78 3 10 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 78 (Polychromatic418967fa.accept_16_13_1_14_1_2855 29 33 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 78 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 33 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 78 3 9 11 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 78
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 33 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 78 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 33 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 78 3 8 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 78
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 33 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 78 3 7 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 78 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 33 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 78 3 6 11 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 78
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 33 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 78 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 33 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 78 3 5 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 78 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 33 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 78
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 33 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 78 3 4 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 78 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 33 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 78 3 3 11 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 78
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 33 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 78 3 2 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 78 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 33 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 78
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 33 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 78 3 1 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 78 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 33 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 78 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 33 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 78)))))))))))))))))))))))))))))))))
  (allB_succ 32 78 (allA_succ_of_accept 31 32 78 (accept_3_4 31 32 78 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 32 78 2 15 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 32 78 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 32 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 32 78 2 14 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 32 78 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 32 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 78 2 13 16 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 78 (accept_3_4 25 32 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 78 2 12 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 78 (Polychromatic418967fa.accept_25_23_7_3_1_2854
  23 32 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 78 2 11 16 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 78
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 32 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 78 2 10 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 78 (accept_3_4 19 32 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 78
  2 9 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 32
  78 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 32 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 32 78 2 8 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 32 78 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 32 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 78 2 7 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 78 (accept_3_4 13 32 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 32 78 2 6 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 32 78 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 32 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 78 2 5 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 78 (Polychromatic418967fa.accept_11_9_10_1_1_581 9
  32 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 78 2 4 16 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 78 (accept_3_4 7 32
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 78 2 3 16 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32 78
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 32 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 78 2 2 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 78 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 32 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 78 2 1 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 78 (accept_3_4 1 32 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 78)))))))))))))))))))))))))))))))) (allB_succ 31 78 (allA_succ_of_accept 30 31 78
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 31 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 78 (accept_3_5 29 31 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 31
  78 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 31 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 31 78 (Polychromatic418967fa.accept_18_9_13_6_1_877 27 31 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 78 (accept_3_5 26 31 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 31 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 78 (Polychromatic418967fa.accept_17_7_14_10_1_1846
  24 31 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 78 (accept_3_5 23 31
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 78
  (Polychromatic418967fa.accept_17_5_14_10_1_2831 22 31 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 31 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 78 (accept_3_5 20 31 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 31 78 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 31 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 78 (Polychromatic418967fa.accept_7_4_3_1_1_87 18
  31 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 78 (accept_3_5 17 31 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 78 (Polychromatic418967fa.accept_7_2_3_1_1_10 16
  31 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 78
  (Polychromatic418967fa.accept_30_15_1_18_1_2853 15 31 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 78 (accept_3_5 14 31 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31
  78 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 31 78 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 31 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 78 (accept_3_5 11 31 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 31 78 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 31 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 78 (accept_3_5 8 31 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 78 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 31
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 78
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 6 31 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 78 (accept_3_5 5 31 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 78
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 31 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 78 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 31 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 78 (accept_3_5 2 31 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 78))))))))))))))))))))))))))))))) (allB_succ 30 78
  (allA_succ_of_accept 29 30 78 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 30 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 78 2 14 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 30 78 3 9 10 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 30 78 2 13 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 78 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 30 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 78 6 4 5 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 78
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 30 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 78 2 11 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 30 78 3 7 10 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 30 78 2 10 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 78 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 30 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 78 6 3 5 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 78 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 30 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 78 2 8 15 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 78 3 5 10 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 78 2 7 15 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 78
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 30 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 78 6 2 5 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 78 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 30 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 78 2 5 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 78 3 3 10 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 30 78 2 4 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 78 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 30 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 78 6 1 5 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 78
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 30 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 30 78 2 2 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 30 78 3 1 10 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 30 78 2 1 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 78 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 30 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 78)))))))))))))))))))))))))))))) (allB_succ 29 78 (allA_succ_of_accept 28
  29 78 (accept_3_4 28 29 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 78
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 78 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 29 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 78 (accept_3_4 25 29 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 78 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 29 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  29 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 78 (accept_3_4 22 29 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 78 (Polychromatic418967fa.accept_9_3_2_6_1_264 21
  29 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 78
  (Polychromatic418967fa.accept_23_20_6_9_1_2851 20 29 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 78 (accept_3_4 19 29 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29
  78 (Polychromatic418967fa.accept_19_18_10_2_1_2850 18 29 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 78 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 29 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 78 (accept_3_4 16 29 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 78
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 29 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 78 (accept_3_4 13 29 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29
  78 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 29 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 29 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 78 (accept_3_4 10 29 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 29 78 (Polychromatic418967fa.accept_14_9_1_8_1_2849 9 29 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 78 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 29
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 78 (accept_3_4 7 29 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 78 (Polychromatic418967fa.accept_11_6_7_1_1_564 6
  29 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 78
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 29 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 78 (accept_3_4 4 29 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 78
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 78 (Polychromatic418967fa.accept_14_2_1_8_1_650 2 29 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 78 (accept_3_4 1 29 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 78))))))))))))))))))))))))))))) (allB_succ 28 78 (allA_succ_of_accept 27 28 78
  (Polychromatic418967fa.accept_11_5_6_1_1_988 27 28 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 78 2 13 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 28 78 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 28 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 78 2 12 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 78 (accept_3_5 23 28 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 28 78 2 11 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 28 78 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 28 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 78 2 10 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 78 (Polychromatic418967fa.accept_21_19_7_15_1_2848
  19 28 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 78 2 9 14 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 78 (accept_3_5 17 28
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28 78 2 8 14 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 28 78
  (Polychromatic418967fa.accept_12_3_4_6_1_434 15 28 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 28 78 2 7 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 28 78 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 28 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 78 2 6 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 78 (accept_3_5 11 28 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 28 78 2 5 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 28 78 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 28 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 78 2 4 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 78 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 28
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 78 2 3 14 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 78 (accept_3_5 5 28
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 78 2 2 14 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 78
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 28 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 78 2 1 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 78 (Polychromatic418967fa.accept_15_1_13_3_1_2002 1 28 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 78)))))))))))))))))))))))))))) (allB_succ 27 78 (allA_succ_of_accept 26
  27 78 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 27 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 27 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 78 3 8 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 78 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 27
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 78
  (Polychromatic418967fa.accept_12_10_3_6_1_882 22 27 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 78 3 7 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 78 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 27 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 78 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 27 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 78 3 6 9 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 78 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 27 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 78 3 5 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 78 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 27 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 78 3 4 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 78 (Polychromatic418967fa.accept_19_11_8_2_1_2847 11 27 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 78 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 27 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 78 3 3 9 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 78
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 27 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 78 (Polychromatic418967fa.accept_14_7_13_8_1_2067 7 27 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 78 3 2 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 78
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 27 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 78 3 1 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 78 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 27 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 78))))))))))))))))))))))))))) (allB_succ 26
  78 (allA_succ_of_accept 25 26 78 (accept_3_4 25 26 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  78 2 12 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 78 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 26 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 78 2 11 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 26 78 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 26 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 78 2 10 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 78 (accept_3_4 19 26 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 78 2 9 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 26 78 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 26 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 78 2 8 13 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 78
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 26 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 78 2 7 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 13 26 78 13 1 2 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 26 78 2 6 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 26 78 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 26 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 26 78 2 5 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 26 78 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 26 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 78 2 4 13 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 78 (accept_3_4 7 26 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 78 2 3 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26 78 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 26 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 78 2 2 13 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 78
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 26 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 78 2 1 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 78 (accept_3_4 1 26 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  78)))))))))))))))))))))))))) (allB_succ 25 78 (allA_succ_of_accept 24 25 78 (Polychromatic418967fa.accept_7_3_4_1_1_71
  24 25 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 78 (accept_3_5 23 25
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 78 (Polychromatic418967fa.accept_9_4_7_6_1_255
  22 25 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 78
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 25 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 25 78 (accept_3_5 20 25 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25
  78 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 25 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 78 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 25 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 78 (accept_3_5 17 25 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 78 (Polychromatic418967fa.accept_20_16_5_18_1_2846 16 25 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  25 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 78 (accept_3_5 14 25 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 78 (Polychromatic418967fa.accept_9_4_7_6_1_255 13
  25 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 78
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 25 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 78 (accept_3_5 11 25 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 25
  78 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 25 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 25 78 (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 25 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 78 (accept_3_5 8 25 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 25 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 78 (Polychromatic418967fa.accept_15_6_10_3_1_2844 6
  25 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 78 (accept_3_5 5 25 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 78 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 25
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 78
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 78 (accept_3_5 2 25 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 78
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 25 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 78))))))))))))))))))))))))) (allB_succ 24 78 (allA_succ_of_accept 23 24 78
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 24 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 24 78 2 11 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 24 78 3 7 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 24 78 2 10 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 78 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 24 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 78 6 3 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 78 (Polychromatic418967fa.accept_19_17_5_2_1_2843 17 24 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 78 2 8 12 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 24 78 3 5 8 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 24 78 2 7 12 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 78
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 24 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 78 6 2 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 78 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 24 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 78 2 5 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 78 3 3 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 78 2 4 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 78 (Polychromatic418967fa.accept_19_7_5_2_1_2842 7 24 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 78 6 1 4 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 78
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 24 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 78 2 2 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 24 78 3 1 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 24 78 2 1 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 24 78 (Polychromatic418967fa.accept_17_1_7_10_1_1835 1 24 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 78)))))))))))))))))))))))) (allB_succ 23 78 (allA_succ_of_accept 22 23 78
  (accept_3_4 22 23 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 78 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 23 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 78 (accept_3_4 19 23 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 78 (Polychromatic418967fa.accept_19_18_4_2_1_2841 18 23 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 78 (accept_3_4 16 23 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 78 (Polychromatic418967fa.accept_10_5_3_8_1_1165
  15 23 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 78
  (Polychromatic418967fa.accept_19_14_4_2_1_2840 14 23 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 78 (accept_3_4 13 23 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23
  78 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 23 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 23 78 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 23 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 78 (accept_3_4 10 23 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 23 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 78 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 23
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 78 (accept_3_4 7 23 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 78 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 23
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 78 (accept_3_4 4 23 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 78
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 23 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 78 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 23 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 78 (accept_3_4 1 23 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 78))))))))))))))))))))))) (allB_succ 22 78 (allA_succ_of_accept 21 22 78
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 22 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 78 2 10 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 78 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 22 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 78 2 9 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 78 (accept_3_5 17 22 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 78 2 8 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 78 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 22 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 78 2 7 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 78 (Polychromatic418967fa.accept_17_13_5_10_1_2839
  13 22 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 78 2 6 11 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 78 (accept_3_5 11 22
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 78 2 5 11 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 78
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 22 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 78 2 4 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 78 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 22 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 78 2 3 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 78 (accept_3_5 5 22 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 78 2 2 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 78 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 22 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 78 2 1 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 78 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 22 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 78)))))))))))))))))))))) (allB_succ 21 78
  (allA_succ_of_accept 20 21 78 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 21 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 78 3 6 7 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 78
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 21 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 78 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 21 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 78 3 5 7 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 78 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 21 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 78
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 21 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 78 3 4 7 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 78 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 21 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 78 3 3 7 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 78
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 21 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 78 3 2 7 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 78 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 21 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 78
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 21 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 78 3 1 7 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 78 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 21 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 78 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 21 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 78))))))))))))))))))))) (allB_succ 20 78
  (allA_succ_of_accept 19 20 78 (accept_3_4 19 20 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 78
  2 9 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20
  78 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 20 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 78 2 8 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 78 (Polychromatic418967fa.accept_12_3_8_6_1_895 15 20 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 78 2 7 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 78 (accept_3_4 13 20 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 78 2 6 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 78 (Polychromatic418967fa.accept_17_11_3_10_1_2838 11 20 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 78 2 5 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 78 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 20
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 78 2 4 10 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 78 (accept_3_4 7 20
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 78 2 3 10 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20 78
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 20 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 78 2 2 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 78 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 20 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 78 2 1 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 78 (accept_3_4 1 20 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 78)))))))))))))))))))) (allB_succ 19 78 (allA_succ_of_accept 18 19 78
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 19 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 78 (accept_3_5 17 19 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19
  78 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 19 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 19 78 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 19 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 78 (accept_3_5 14 19 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 19 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 78 (Polychromatic418967fa.accept_9_3_1_6_1_86 12
  19 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 78 (accept_3_5 11 19 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 78 (Polychromatic418967fa.accept_7_3_5_1_1_72 10
  19 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 19 78 (accept_3_5 8 19 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 78
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 19 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 19 78 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 19 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 78 (accept_3_5 5 19 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 19 78 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 19 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 78 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 19
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 78 (accept_3_5 2 19 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 78))))))))))))))))))) (allB_succ 18 78
  (allA_succ_of_accept 17 18 78 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 18 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 78 2 8 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 18 78 3 5 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 18 78 2 7 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 18 78 (Polychromatic418967fa.accept_21_13_18_15_1_2837 13 18 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 78 6 2 3 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 78
  (Polychromatic418967fa.accept_14_11_4_8_1_664 11 18 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 18 78 2 5 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 18 78 3 3 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 18 78 2 4 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 18 78 (Polychromatic418967fa.accept_17_7_1_10_1_2836 7 18 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 78 6 1 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 78 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 18 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 78 2 2 9 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 78 3 1 6 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 78 2 1 9 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 78
  (Polychromatic418967fa.accept_19_1_18_2_1_2835 1 18 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 78)))))))))))))))))) (allB_succ 17 78 (allA_succ_of_accept 16 17 78 (accept_3_4 16 17 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 78
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 17 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 78 (accept_3_4 13 17 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 17
  78 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 17 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 17 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 78 (accept_3_4 10 17 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 17 78 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 17 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 78 (Polychromatic418967fa.accept_21_8_17_15_1_2834
  8 17 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 78 (accept_3_4 7 17 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 78 (Polychromatic418967fa.accept_21_6_17_15_1_2833
  6 17 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 78
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 17 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 78 (accept_3_4 4 17 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 78
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 78 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 17 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 78 (accept_3_4 1 17 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 78))))))))))))))))) (allB_succ 16 78 (allA_succ_of_accept 15 16 78
  (Polychromatic418967fa.accept_12_3_4_6_1_434 15 16 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 78 2 7 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 78 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 16 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 78 2 6 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 78 (accept_3_5 11 16 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 78 2 5 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 78 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 16 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 78 2 4 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 78 (Polychromatic418967fa.accept_17_7_16_10_1_1849 7
  16 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 78 2 3 8 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 78 (accept_3_5 5 16
  78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 78 2 2 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 78 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 16
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 16 78 2 1 8 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 16 78
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 16 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 78)))))))))))))))) (allB_succ 15 78 (allA_succ_of_accept 14 15 78
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 15 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 78 3 4 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 78 (Polychromatic418967fa.accept_18_11_15_6_1_2832 11 15 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 78
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 15 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 78 3 3 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 78 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 15 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 78 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 15 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 78 3 2 5 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 78 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 15 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 78 3 1 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 78 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 15 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 78
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 78))))))))))))))) (allB_succ 14 78 (allA_succ_of_accept 13 14 78 (accept_3_4 13 14 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 78 2 6 7 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 14 78 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 14 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 78 2 5 7 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 78
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 14 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 14 78 2 4 7 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 14 78 (accept_3_4 7 14 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 14 78 2
  3 7 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14 78
  (Polychromatic418967fa.accept_17_5_14_10_1_2831 5 14 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 14 78 2 2 7 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 14 78 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 14 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 78 2 1 7 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 78 (accept_3_4 1 14 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 78)))))))))))))) (allB_succ 13 78 (allA_succ_of_accept 12 13 78
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 13 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 78 (accept_3_5 11 13 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13
  78 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 13 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 13 78 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 13 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 78 (accept_3_5 8 13 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 13 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 78 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6
  13 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 78 (accept_3_5 5 13 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13 78 (Polychromatic418967fa.accept_22_4_13_12_1_2830
  4 13 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 78
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 13 78 (accept_3_5 2 13 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 78
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 13 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 13 78))))))))))))) (allB_succ 12 78 (allA_succ_of_accept 11 12 78
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 12 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 78 2 5 6 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 12 78 3 3 4 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 12 78 2 4 6 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 78 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 12 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 78 6 1 2 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 78 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 12 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 78 2 2 6 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 12 78 3 1 4 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 12 78 2 1 6 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 78
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 12 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 78)))))))))))) (allB_succ 11 78 (allA_succ_of_accept 10 11 78 (accept_3_4 10 11 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 78
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 11 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 78 (accept_3_4 7 11 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11 78
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 6 11 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 78 (accept_3_4 4 11 78 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 11 78 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 11 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 78 (Polychromatic418967fa.accept_23_2_11_9_1_2829 2 11 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 78 (accept_3_4 1 11 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 11 78))))))))))) (allB_succ 10 78 (allA_succ_of_accept 9 10 78
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 10 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 78 2 4 5 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 78 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 10 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 78 2 3 5 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 78 (accept_3_5 5 10 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 10 78 2 2 5 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 10 78 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 10 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 78 2 1 5 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 78 (Polychromatic418967fa.accept_21_1_10_15_1_2828 1
  10 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 78)))))))))) (allB_succ 9 78
  (allA_succ_of_accept 8 9 78 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 9 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 78 3 2 3 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 78
  (Polychromatic418967fa.accept_15_5_9_3_1_528 5 9 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 78 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 9 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 78 3 1 3 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 78 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 9 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 78
  (Polychromatic418967fa.accept_10_1_9_8_1_123 1 9 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 78))))))))) (allB_succ 8 78 (allA_succ_of_accept 7 8 78 (accept_3_4 7 8 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 8 78 2 3 4 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 8 78 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 8 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 78 2 2 4 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 78 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 8 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 78 2 1 4 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 78 (accept_3_4 1 8 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 8 78)))))))) (allB_succ 7 78 (allA_succ_of_accept 6 7 78
  (Polychromatic418967fa.accept_11_6_7_1_1_564 6 7 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 78 (accept_3_5 5 7 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 78
  (Polychromatic418967fa.accept_9_4_7_6_1_255 4 7 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 78 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 7 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 78 (accept_3_5 2 7 78 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 7 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 7 78))))))) (allB_succ 6 78 (allA_succ_of_accept 5 6 78
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 6 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 6 78 2 2 3 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 6 78 3 1 2 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 6 78 2 1 3 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 78 (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 6 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 78)))))) (allB_succ 5 78 (allA_succ_of_accept 4 5 78 (accept_3_4 4 5 78
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 78 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 5 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 78
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 5 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 78 (accept_3_4 1 5 78 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 78))))) (allB_succ
  4 78 (allA_succ_of_accept 3 4 78 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 4 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 78 2 1 2 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 78 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 4 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 4 78)))) (allB_succ 3 78 (allA_succ_of_accept 2 3 78
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 3 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 78 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 3 78))) (allB_succ 2 78 (allA_succ_of_accept 1 2 78 (accept_3_4 1 2 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 2 78)) (allB_two
  78))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


