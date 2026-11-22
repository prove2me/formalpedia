-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch115
-- name    : Polychromatic418967fa_Branch115
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:11:05.756255+00:00
-- url     : https://prove2.me/theorems/05b80032-6417-4112-825f-691fe606fa03
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

def Polychromatic418967fa.branch_115 : allB 115 115 :=
  allB_succ' 2 114 115 (Eq.refl Bool.true) (allA_succ_of_accept 1 114 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  114 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 115)) (allB_succ' 3 113 115
  (Eq.refl Bool.true) (allA_of_3_1 3 113 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 112 115 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 112 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 115 (accept_3_3 2 112 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 112 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 112 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 115)))) (allB_succ' 5 111 115 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 111 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 115 (Polychromatic418967fa.accept_13_3_7_11_1_1904 3 111
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 115 (accept_3_3 2 111 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 1
  111 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111 115))))) (allB_succ' 6 110 115
  (Eq.refl Bool.true) (allA_of_3_1 6 110 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 109 115 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 109 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 115 (accept_3_3 5 109 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 109 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 115
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 109 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 115 (accept_3_3 2 109 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 115 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 109 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 115))))))) (allB_succ' 8 108 115 (Eq.refl Bool.true) (allA_succ_of_accept 7 108 115
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 108 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 108 115 (Polychromatic418967fa.accept_13_6_4_11_1_282 6 108 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 115 (accept_3_3 5 108 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 108 115 (Polychromatic418967fa.accept_16_4_12_3_1_2180 4 108 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 115
  (Polychromatic418967fa.accept_10_3_8_5_1_606 3 108 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 108 115 (accept_3_3 2 108 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  108 115 (Polychromatic418967fa.accept_21_1_3_10_1_5401 1 108 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 108 115)))))))) (allB_succ' 9 107 115 (Eq.refl Bool.true) (allA_of_3_1 9 107 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 106 115 (Eq.refl Bool.true) (allA_succ_of_accept 9 106 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 106 115 (accept_3_3 8 106 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  106 115 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 106 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 106 115 (Polychromatic418967fa.accept_15_6_1_10_1_1549 6 106 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 106 115 (accept_3_3 5 106 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 106 115 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 106 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 106 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 106 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 106 115 (accept_3_3 2 106 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  106 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 106 115)))))))))) (allB_succ' 11 105 115 (Eq.refl Bool.true) (allA_succ_of_gcd 10 105 115 5 2 21
  23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 105 115
  (Polychromatic418967fa.accept_13_9_1_11_1_275 9 105 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 115 (accept_3_3 8 105 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  105 115 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 105 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 105 115 5 1 21 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4
  105 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 115
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 105 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 105 115 (accept_3_3 2 105 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  105 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 105 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 105 115))))))))))) (allB_succ' 12 104 115 (Eq.refl Bool.true) (allA_of_3_1 12 104 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 103 115 (Eq.refl Bool.true) (allA_succ_of_accept 12 103 115
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 103 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 115 (accept_3_3 11 103 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 103 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 115 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 103 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 115 (accept_3_3 8 103 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 115 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 103 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 115
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 103 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 115 (accept_3_3 5 103 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 115 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 103 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 115 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 103 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 115 (accept_3_3 2 103 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 115 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 103 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103 115))))))))))))) (allB_succ' 14 102 115 (Eq.refl
  Bool.true) (allA_succ_of_accept 13 102 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 115
  (Polychromatic418967fa.accept_19_12_7_1_1_5400 12 102 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 102 115 (accept_3_3 11 102 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 102 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 102 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 102 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 115 (accept_3_3 8 102 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 115 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 102 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 115
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 102 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 115 (accept_3_3 5 102 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 115 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 102 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 115 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 102 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 115 (accept_3_3 2 102 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 115)))))))))))))) (allB_succ' 15 101 115 (Eq.refl
  Bool.true) (allA_of_3_1 15 101 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 100 115 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 100 115 5 3 20 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 100 115 (accept_3_3 14 100 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 100 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 100 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 100 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 100 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 115 (accept_3_3 11 100 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 115 5 2 20 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 100 115 (accept_3_3 8 100 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 100 115 (Polychromatic418967fa.accept_8_7_4_3_1_156 7
  100 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 115
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 100 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 100 115 5 1 20 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 100 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 100 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 115 (accept_3_3 2 100 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 100 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  100 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 115)))))))))))))))) (allB_succ' 17
  99 115 (Eq.refl Bool.true) (allA_succ_of_accept 16 99 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 115
  (Polychromatic418967fa.accept_19_15_4_1_1_4060 15 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 115 (accept_3_3 14 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 115 (Polychromatic418967fa.accept_22_13_11_5_1_1252 13 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 99 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 115 (accept_3_3 11 99 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 99 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 115
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 115 (accept_3_3 8 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  115 (Polychromatic418967fa.accept_19_7_4_1_1_5399 7 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 115 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 99 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 115 (accept_3_3 5 99 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 115
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 3 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 115 (accept_3_3 2 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  115 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 99 115))))))))))))))))) (allB_succ' 18 98 115 (Eq.refl Bool.true) (allA_of_3_1 18 98 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 19 97 115 (Eq.refl Bool.true) (allA_succ_of_accept 18 97 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 115 (accept_3_3 17 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 115 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 115 (Polychromatic418967fa.accept_19_15_2_1_1_2822 15 97 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 115 (accept_3_3 14 97 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 115 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 97 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 115
  (Polychromatic418967fa.accept_10_2_7_5_1_605 12 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 115 (accept_3_3 11 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 115 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 97 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 115 (accept_3_3 8 97 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 115 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 97 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 115 (accept_3_3 5 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  115 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 115 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 97 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 115 (accept_3_3 2 97 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 115 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 97 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 115))))))))))))))))))) (allB_succ' 20 96 115 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 96 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 96 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 115 (Polychromatic418967fa.accept_15_3_6_10_1_1539 18 96
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 96 115 (accept_3_3 17 96 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 115 (Polychromatic418967fa.accept_7_2_5_3_1_98 16
  96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 96 115
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 96 115 (accept_3_3 14 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  96 115 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 96 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 96 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 115 (accept_3_3 11 96 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 96 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 96 115
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 96 115 (accept_3_3 8 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96
  115 (Polychromatic418967fa.accept_13_7_5_11_1_1927 7 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 96 115 (Polychromatic418967fa.accept_13_6_5_11_1_1971 6 96 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 115 (accept_3_3 5 96 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 115 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 96 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96 115
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 115 (accept_3_3 2 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96
  115 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 115)))))))))))))))))))) (allB_succ' 21 95 115 (Eq.refl Bool.true) (allA_of_3_1 21 95 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 94 115 (Eq.refl Bool.true) (allA_succ_of_accept 21 94 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 115 (accept_3_3 20 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 115 (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 94 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 115 (accept_3_3 17 94 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 115 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 94 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 115 (accept_3_3 14 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 115 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 94 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 115 (accept_3_3 11 94 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 94 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 115 (accept_3_3 8 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  115 (Polychromatic418967fa.accept_13_7_3_11_1_280 7 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 94 115 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 94 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 115 (accept_3_3 5 94 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 94 115 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 94 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 94 115 (accept_3_3 2 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94
  115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 115)))))))))))))))))))))) (allB_succ' 23 93 115 (Eq.refl Bool.true) (allA_succ_of_accept 22 93 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 93 115 (Polychromatic418967fa.accept_15_6_3_10_1_2341 21 93 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 115 (accept_3_3 20 93 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 93 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 93 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 115 (accept_3_3 17 93
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 115 (Polychromatic418967fa.accept_6_4_3_1_1_57
  16 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 115
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 115 (accept_3_3 14 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 93 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 115 (accept_3_3 11 93 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 115
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 115 (accept_3_3 8 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  115 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 115 (accept_3_3 5 93 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 115 (Polychromatic418967fa.accept_12_3_9_7_1_472 3
  93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 115 (accept_3_3 2 93 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 115)))))))))))))))))))))))
  (allB_succ' 24 92 115 (Eq.refl Bool.true) (allA_of_3_1 24 92 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  25 91 115 (Eq.refl Bool.true) (allA_succ_of_accept 24 91 115 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 91 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 115 (accept_3_3 23 91 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 22
  91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 115
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 115 (accept_3_3 20 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 115 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 115 (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 91 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 115 (accept_3_3 17 91 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 115 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 91 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 115
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 115 (accept_3_3 14 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 115 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 91 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 115 (accept_3_3 11 91 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 115 (Polychromatic418967fa.accept_14_10_7_3_1_1022 10 91 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 115
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 115 (accept_3_3 8 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  115 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 91 115 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 91 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 115 (accept_3_3 5 91 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 91 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 115
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 115 (accept_3_3 2 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  115 (Polychromatic418967fa.accept_21_1_7_10_1_2596 1 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 91 115))))))))))))))))))))))))) (allB_succ' 26 90 115 (Eq.refl Bool.true) (allA_succ_of_gcd 25
  90 115 5 5 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 90 115 (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 90 115 (accept_3_3 23 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 115 (Polychromatic418967fa.accept_20_2_10_15_1_3953 22 90 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 115 5 4 18 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 115
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 90 115 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 90 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 115 (accept_3_3 17 90 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 90 115 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 90 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 115 5 3 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 115 (accept_3_3 14 90 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 115
  (Polychromatic418967fa.accept_16_12_10_3_1_4209 12 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 90 115 (accept_3_3 11 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90
  115 5 2 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  90 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 90 115 (accept_3_3 8 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90
  115 (Polychromatic418967fa.accept_13_7_12_11_1_1911 7 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 90 115 (Polychromatic418967fa.accept_19_6_14_1_1_2752 6 90 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 90 115 5 1 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 90 115 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 90
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 115
  (Polychromatic418967fa.accept_20_3_10_15_1_620 3 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 90 115 (accept_3_3 2 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90
  115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 115)))))))))))))))))))))))))) (allB_succ' 27 89 115 (Eq.refl Bool.true) (allA_of_3_1 27 89 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 88 115 (Eq.refl Bool.true) (allA_succ_of_accept 27 88 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 88 115 (accept_3_3 26 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  88 115 (Polychromatic418967fa.accept_13_12_10_11_1_1279 25 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 88 115 (Polychromatic418967fa.accept_19_5_12_1_1_2817 24 88 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 115 (accept_3_3 23 88 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 88 115 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 88 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 88 115 (accept_3_3 20 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  88 115 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 88 115 (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 88 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 115 (accept_3_3 17 88 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 115 (Polychromatic418967fa.accept_13_3_10_11_1_1293 16 88
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 88 115 (accept_3_3 14 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  88 115 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 88 115 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 88 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 115 (accept_3_3 11 88 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 115 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 88 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 115 (accept_3_3 8 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  115 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 88 115 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 88 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 115 (accept_3_3 5 88 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 88 115 (Polychromatic418967fa.accept_13_4_10_11_1_1908 4 88 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 88 115 (accept_3_3 2 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88
  115 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 115)))))))))))))))))))))))))))) (allB_succ' 29 87 115 (Eq.refl Bool.true) (allA_succ_of_accept 28 87 115
  (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 87 115 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 87 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 115 (accept_3_3 26 87 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 87 115 (Polychromatic418967fa.accept_16_9_7_3_1_614 25 87 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 115 (Polychromatic418967fa.accept_15_9_12_10_1_809
  24 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 115 (accept_3_3 23
  87 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 115
  (Polychromatic418967fa.accept_6_4_3_1_1_57 22 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 87 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 87 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 115 (accept_3_3 20 87 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 87 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 87 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 115 (Polychromatic418967fa.accept_10_8_7_5_1_602
  18 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 115 (accept_3_3 17
  87 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 115
  (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 87 115 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 87 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 115 (accept_3_3 14 87 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 87 115 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 87 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 115 (Polychromatic418967fa.accept_8_4_7_3_1_144 12
  87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 115 (accept_3_3 11 87
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 115 (Polychromatic418967fa.accept_6_4_3_1_1_57
  10 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 115
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 115 (accept_3_3 8 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  115 (Polychromatic418967fa.accept_13_7_9_11_1_705 7 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 87 115 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 87 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 115 (accept_3_3 5 87 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 115
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 115 (accept_3_3 2 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87
  115 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 87 115))))))))))))))))))))))))))))) (allB_succ' 30 86 115 (Eq.refl Bool.true) (allA_of_3_1 30 86 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 85 115 (Eq.refl Bool.true) (allA_succ_of_gcd 30 85 115 5 6 17
  23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 85 115
  (accept_3_3 29 85 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 115
  (Polychromatic418967fa.accept_9_1_4_7_1_7 28 85 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 85 115 (Polychromatic418967fa.accept_13_1_7_11_1_702 27 85 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 115 (accept_3_3 26 85 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 85 115 5 5 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 85 115 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 85 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 115 (accept_3_3 23 85 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 115
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 85 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 85 115 5 4 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 85 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 85 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 115 (accept_3_3 17 85 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 115 (Polychromatic418967fa.accept_7_2_1_3_1_102 16
  85 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 85 115 5 3 17 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 85 115 (accept_3_3 14
  85 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 115
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 85 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 85 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 85 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 115 (accept_3_3 11 85 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 85 115 5 2 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 85 115 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 85 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 115 (accept_3_3 8 85 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 115 (Polychromatic418967fa.accept_20_7_5_15_1_1548 7 85 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 85 115 5 1 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 85 115 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 85 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 115 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 85 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 115 (accept_3_3 2 85 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 85
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 115)))))))))))))))))))))))))))))))
  (allB_succ' 32 84 115 (Eq.refl Bool.true) (allA_succ_of_accept 31 84 115 (Polychromatic418967fa.accept_8_7_4_3_1_156
  31 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 115
  (Polychromatic418967fa.accept_13_4_6_11_1_2017 30 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 84 115 (accept_3_3 29 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  84 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 84 115 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 84 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 115 (accept_3_3 26 84 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 115 (Polychromatic418967fa.accept_20_5_4_15_1_3931 25 84
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 115
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 84 115 (accept_3_3 23 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  84 115 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 84 115 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 84 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 115 (accept_3_3 20 84 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 84 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 115
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 115 (accept_3_3 17 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 115 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 115 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 84 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 115 (accept_3_3 14 84 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 115 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 84 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 115
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 115 (accept_3_3 11 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 115 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 84 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 115 (accept_3_3 8 84 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 115 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 84 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 115
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 115 (accept_3_3 5 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  115 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 84 115 (Polychromatic418967fa.accept_15_3_9_10_1_2325 3 84 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 115 (accept_3_3 2 84 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 84 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 84 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84 115)))))))))))))))))))))))))))))))) (allB_succ' 33 83 115
  (Eq.refl Bool.true) (allA_of_3_1 33 83 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 82 115 (Eq.refl
  Bool.true) (allA_succ_of_accept 33 82 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 115 (accept_3_3 32 82 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 82 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 115
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 115 (accept_3_3 29 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 115 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 82 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 115 (accept_3_3 26 82 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 115
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 115 (accept_3_3 23 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 115 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 115 (accept_3_3 20 82 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 115 (Polychromatic418967fa.accept_13_6_4_11_1_282 19 82 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 115
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 115 (accept_3_3 17 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 115 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 82 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 115 (accept_3_3 14 82 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 115
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 115 (accept_3_3 11 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 115 (Polychromatic418967fa.accept_13_10_4_11_1_1969 10 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 115 (accept_3_3 8 82 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 115 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 82 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 115
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 115 (accept_3_3 5 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  115 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 82 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 115 (accept_3_3 2 82 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 115)))))))))))))))))))))))))))))))))) (allB_succ' 35 81 115
  (Eq.refl Bool.true) (allA_succ_of_accept 34 81 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 115
  (Polychromatic418967fa.accept_13_7_3_11_1_280 33 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 115 (accept_3_3 32 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 115 (Polychromatic418967fa.accept_13_5_3_11_1_1288 31 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 115 (accept_3_3 29 81 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 115
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 115 (accept_3_3 26 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 115 (Polychromatic418967fa.accept_19_6_5_1_1_2765 25 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 115 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 81 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 115 (accept_3_3 23 81 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 115
  (Polychromatic418967fa.accept_11_10_4_5_1_359 21 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 115 (accept_3_3 20 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 115 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 115 (accept_3_3 17 81 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 115
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 115 (accept_3_3 14 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 115 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 115 (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 81 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 115 (accept_3_3 11 81 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 115
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 115 (accept_3_3 8 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  115 (Polychromatic418967fa.accept_13_7_3_11_1_280 7 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 115 (accept_3_3 5 81 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 115
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 115 (accept_3_3 2 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  115 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 115))))))))))))))))))))))))))))))))))) (allB_succ' 36 80 115 (Eq.refl Bool.true) (allA_of_3_1 36 80 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 79 115 (Eq.refl Bool.true) (allA_succ_of_accept 36 79 115
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 115 (accept_3_3 35 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 115 (accept_3_3 32 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 115 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 79 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 115
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 115 (accept_3_3 29 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 115 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 115 (accept_3_3 26 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 115 (Polychromatic418967fa.accept_13_12_1_11_1_1917 25 79 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 115
  (Polychromatic418967fa.accept_10_4_9_5_1_84 24 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 115 (accept_3_3 23 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 115 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 115 (accept_3_3 20 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 79 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 115
  (Polychromatic418967fa.accept_16_2_15_3_1_1300 18 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 115 (accept_3_3 17 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 115 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 115 (accept_3_3 14 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 79 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 115
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 115 (accept_3_3 11 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 115 (Polychromatic418967fa.accept_13_10_1_11_1_1961 10 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 115 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 115 (accept_3_3 8 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 115 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 79 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 115
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 115 (accept_3_3 5 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  115 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 115 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 79 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 115 (accept_3_3 2 79 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 115))))))))))))))))))))))))))))))))))))) (allB_succ' 38 78 115
  (Eq.refl Bool.true) (allA_succ_of_accept 37 78 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 115
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 115 (accept_3_3 35 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 115 (Polychromatic418967fa.accept_19_15_2_1_1_2822 34 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 115 (accept_3_3 32 78 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 115 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 78 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 115
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 115 (accept_3_3 29 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 115 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 78 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 115 (accept_3_3 26 78 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 115
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 24 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 115 (accept_3_3 23 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 115 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 115 (accept_3_3 20 78 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 78 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 115
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 115 (accept_3_3 17 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 115 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 115 (Polychromatic418967fa.accept_19_15_2_1_1_2822 15 78 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 115 (accept_3_3 14 78 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 115
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 115 (accept_3_3 11 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 115 (accept_3_3 8 78 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 115 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 78 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 115
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 115 (accept_3_3 5 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  115 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 78 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 115 (accept_3_3 2 78 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 115)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 77 115
  (Eq.refl Bool.true) (allA_of_3_1 39 77 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 76 115 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 76 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 115 (accept_3_3 38 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 115 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 76 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 115
  (Polychromatic418967fa.accept_15_6_1_10_1_1549 36 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 76 115 (accept_3_3 35 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  76 115 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 76 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 115 (accept_3_3 32 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 115 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 76 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 115
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 115 (accept_3_3 29 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 115 (accept_3_3 26 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 115 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 76 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 115
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 115 (accept_3_3 23 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 115 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 115 (accept_3_3 20 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 76 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 115
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 115 (accept_3_3 17 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 115 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 115 (accept_3_3 14 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 115 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 76 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 115
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 115 (accept_3_3 11 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 115 (accept_3_3 8 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 115 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 76 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 115
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 115 (accept_3_3 5 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  115 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 76 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 115 (accept_3_3 2 76 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 76 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76 115)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 75
  115 (Eq.refl Bool.true) (allA_succ_of_gcd 40 75 115 5 8 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 75 115 (Polychromatic418967fa.accept_16_7_11_3_1_1330 39 75 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 115 (accept_3_3 38 75 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 115 (Polychromatic418967fa.accept_7_2_5_3_1_98 37
  75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 115
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 75 115 5 7 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 75 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 75 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 115 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 75 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 115 (accept_3_3 32 75 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 115 (Polychromatic418967fa.accept_9_4_3_7_1_296 31
  75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 115 5 6 15 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 115 (accept_3_3 29
  75 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 115
  (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 75 115 (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 75 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 115 (accept_3_3 26 75 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 75 115 5 5 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 75 115 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 75 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 115 (accept_3_3 23 75 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 75 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 115
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 75 115 5 4 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 75 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 75 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 115 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 75 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 115 (accept_3_3 17 75 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 115 5 3 15 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 115 (accept_3_3 14
  75 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 115
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 115 (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 75 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 115 (accept_3_3 11 75 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 75 115 5 2 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 75 115 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 75 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 115 (accept_3_3 8 75 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 115 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 75 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 115
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 75 115 5 1 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 75 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 115 (Polychromatic418967fa.accept_13_3_10_11_1_1293 3 75 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 115 (accept_3_3 2 75 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 115 (Polychromatic418967fa.accept_7_1_5_3_1_268 1
  75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  115))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 74 115 (Eq.refl Bool.true) (allA_of_3_1 42 74 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 73 115 (Eq.refl Bool.true) (allA_succ_of_accept 42 73 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 115 (accept_3_3 41 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 115 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 115 (accept_3_3 38 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 115 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 73 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 115
  (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 115 (accept_3_3 35 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 115 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 115 (accept_3_3 32 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 73 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 115 (accept_3_3 29 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 115 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 115 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 115 (accept_3_3 26 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 115 (Polychromatic418967fa.accept_17_8_5_13_1_4158 25 73 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 115
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 115 (accept_3_3 23 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 115 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 115 (accept_3_3 20 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 115 (Polychromatic418967fa.accept_13_6_8_11_1_5398 19 73 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 115 (accept_3_3 17 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 115 (Polychromatic418967fa.accept_13_3_8_11_1_1906 16 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 115 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 115 (accept_3_3 14 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 73 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 115
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 115 (accept_3_3 11 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 115 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 115 (accept_3_3 8 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 115 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 73 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 115 (accept_3_3 5 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  115 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 115 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 73 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 115 (accept_3_3 2 73 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 115 (Polychromatic418967fa.accept_13_1_8_11_1_724 1 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 115))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 72
  115 (Eq.refl Bool.true) (allA_succ_of_accept 43 72 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 72 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 115
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 42 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 72 115 (accept_3_3 41 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  72 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 72 115 (Polychromatic418967fa.accept_15_9_12_10_1_809 39 72 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 115 (accept_3_3 38 72 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 115 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 72 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 115
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 115 (accept_3_3 35 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  72 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 115 (accept_3_3 32 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 115 (Polychromatic418967fa.accept_13_5_7_11_1_3470 31 72 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 115
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 30 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 115 (accept_3_3 29 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 115 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 115 (accept_3_3 26 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 115 (Polychromatic418967fa.accept_13_12_7_11_1_1935 25 72 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 115
  (Polychromatic418967fa.accept_15_9_12_10_1_809 24 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 115 (accept_3_3 23 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 115 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 72 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 115 (accept_3_3 20 72 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 72 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 115
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 115 (accept_3_3 17 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  72 115 (Polychromatic418967fa.accept_13_3_7_11_1_1904 16 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 115 (accept_3_3 14 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 72 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 115
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 115 (accept_3_3 11 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 115 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 115 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 115 (accept_3_3 8 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 115 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 72 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 115
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 115 (accept_3_3 5 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  115 (Polychromatic418967fa.accept_13_4_7_11_1_1981 4 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 72 115 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 115 (accept_3_3 2 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 72 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72 115))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 71 115 (Eq.refl Bool.true) (allA_of_3_1 45 71 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  46 70 115 (Eq.refl Bool.true) (allA_succ_of_gcd 45 70 115 5 9 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 70 115 (accept_3_3 44 70 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 70 115 (Polychromatic418967fa.accept_11_10_4_5_1_359 43 70 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 70 115 (Polychromatic418967fa.accept_13_3_5_11_1_716
  42 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 115 (accept_3_3 41
  70 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70 115 5 8 14 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 70 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 115 (accept_3_3 38 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 115 (Polychromatic418967fa.accept_16_4_6_3_1_1311 36 70 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 70 115 5 7 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 70 115 (Polychromatic418967fa.accept_16_2_6_3_1_5396
  34 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 115 (accept_3_3 32 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 115 (Polychromatic418967fa.accept_19_12_13_1_1_2779 31 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 70 115 5 6 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 70 115 (accept_3_3 29 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 70 115 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 70 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 70 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 115 (accept_3_3 26 70 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 70 115 5 5 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 70 115 (Polychromatic418967fa.accept_17_7_2_13_1_5397
  24 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 115 (accept_3_3 23
  70 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 115
  (Polychromatic418967fa.accept_18_4_16_7_1_1873 22 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 70 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 115 5 4 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 115 (Polychromatic418967fa.accept_13_6_5_11_1_1971 19 70 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 115
  (Polychromatic418967fa.accept_16_2_6_3_1_5396 18 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 70 115 (accept_3_3 17 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  70 115 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 70 115 5 3 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 70 115 (accept_3_3 14 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 70 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 115 (Polychromatic418967fa.accept_19_12_13_1_1_2779 12 70
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 115 (accept_3_3 11 70 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 115 5 2 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 115 (accept_3_3 8 70 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 115 (Polychromatic418967fa.accept_13_7_5_11_1_1927
  7 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 115
  (Polychromatic418967fa.accept_13_6_5_11_1_1971 6 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 70 115 5 1 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 70 115 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 70 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 70 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 115 (accept_3_3 2 70 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  115)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 69 115 (Eq.refl Bool.true) (allA_succ_of_gcd 46 69
  115 23 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  69 115 (Polychromatic418967fa.accept_13_6_4_11_1_282 45 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 69 115 (accept_3_3 44 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 115 (Polychromatic418967fa.accept_19_5_12_1_1_2817 43 69 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 115 (accept_3_3 41 69 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 40
  69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 115
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 115 (accept_3_3 38 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 115 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 115 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 69 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 115 (accept_3_3 35 69 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 115
  (Polychromatic418967fa.accept_13_7_4_11_1_1967 33 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 115 (accept_3_3 32 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 115 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 115 (accept_3_3 29 69 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 115
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 115 (accept_3_3 26 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 115 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 115 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 69 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 23 69 115 23 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 22 69 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 22
  69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 115
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 115 (accept_3_3 20 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 115 (accept_3_3 17 69 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 115
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 115 (accept_3_3 14 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 115 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 69 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 115 (accept_3_3 11 69 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 115
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 115 (accept_3_3 8 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  115 (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 69 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 115 (accept_3_3 5 69 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 115
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 115 (accept_3_3 2 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69
  115 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 115))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 68 115 (Eq.refl Bool.true) (allA_of_3_1
  48 68 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 67 115 (Eq.refl Bool.true) (allA_succ_of_accept 48
  67 115 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 67 115 (accept_3_3 47 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 67 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 67 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 67 115 (Polychromatic418967fa.accept_19_7_10_1_1_5382 45 67
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 115 (accept_3_3 44 67 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 115 (Polychromatic418967fa.accept_7_1_4_3_1_21 43
  67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 115
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 115 (accept_3_3 41 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 115 (Polychromatic418967fa.accept_18_4_13_7_1_5395 40 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 115 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 115 (accept_3_3 38 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 67 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 115
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 115 (accept_3_3 35 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 115 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 115 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 115 (accept_3_3 32 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 115 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 67 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 115
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 115 (accept_3_3 29 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 115 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 115 (accept_3_3 26 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 115 (Polychromatic418967fa.accept_19_6_10_1_1_5394 25 67 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 115
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 115 (accept_3_3 23 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 115 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 115 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 115 (accept_3_3 20 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 67 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 115
  (Polychromatic418967fa.accept_10_8_7_5_1_602 18 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 115 (accept_3_3 17 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 115 (Polychromatic418967fa.accept_13_3_2_11_1_1999 16 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 115 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 115 (accept_3_3 14 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 115 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 67 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 115
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 115 (accept_3_3 11 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 115 (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 115 (accept_3_3 8 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 115 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 67 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 115
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 115 (accept_3_3 5 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  115 (Polychromatic418967fa.accept_13_4_2_11_1_733 4 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 115 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 115 (accept_3_3 2 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 115 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 67 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 115)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 66 115 (Eq.refl Bool.true) (allA_succ_of_accept 49 66 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 115
  (Polychromatic418967fa.accept_13_9_1_11_1_275 48 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 66 115 (accept_3_3 47 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  66 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 66 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 66 115 (accept_3_3 44 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 115 (Polychromatic418967fa.accept_19_5_9_1_1_5393 43 66 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 115
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 66 115 (accept_3_3 41 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  66 115 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 66 115 (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 115 (accept_3_3 38 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 115
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 66 115 (accept_3_3 35 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  66 115 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 66 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 115 (accept_3_3 32 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 115 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 66 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 115
  (Polychromatic418967fa.accept_19_11_9_1_1_2809 30 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 66 115 (accept_3_3 29 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  66 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 66 115 (Polychromatic418967fa.accept_14_13_10_3_1_1037 27 66 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 115 (accept_3_3 26 66 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 115
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 66 115 (accept_3_3 23 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  66 115 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 66 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 115 (accept_3_3 20 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 66 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 115
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 18 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 66 115 (accept_3_3 17 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  66 115 (Polychromatic418967fa.accept_13_3_1_11_1_1268 16 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 66 115 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 66 115 (accept_3_3 14 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 115
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 12 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 66 115 (accept_3_3 11 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  66 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 66 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 115 (accept_3_3 8 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 115 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 66 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 115
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 115 (accept_3_3 5 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66
  115 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 66 115 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 66 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 115 (accept_3_3 2 66 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 66 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66 115))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 65 115 (Eq.refl Bool.true) (allA_of_3_1 51 65 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  52 64 115 (Eq.refl Bool.true) (allA_succ_of_accept 51 64 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 64 115 (accept_3_3 50 64 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 64 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 49
  64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 64 115
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 64 115 (accept_3_3 47 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  64 115 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 64 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 64 115 (accept_3_3 44 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 64 115 (Polychromatic418967fa.accept_13_4_12_11_1_5362 43 64 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 64 115
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 64 115 (accept_3_3 41 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  64 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 64 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 115 (accept_3_3 38 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 64 115 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 64 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 115
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 64 115 (accept_3_3 35 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  64 115 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 64 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 115 (accept_3_3 32 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 64 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 64 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 115
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 64 115 (accept_3_3 29 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  64 115 (Polychromatic418967fa.accept_15_13_4_10_1_821 28 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 64 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 115 (accept_3_3 26 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 64 115 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 64 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 115
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 64 115 (accept_3_3 23 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  64 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 64 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 115 (accept_3_3 20 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 64 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 64 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 115
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 64 115 (accept_3_3 17 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  64 115 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 64 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 115 (accept_3_3 14 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 64 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 64 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 115
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 64 115 (accept_3_3 11 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  64 115 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 64 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 115 (accept_3_3 8 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 64 115 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 64 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 115
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 64 115 (accept_3_3 5 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64
  115 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 64 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 115 (accept_3_3 2 64 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 64 115 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64 115))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 63 115 (Eq.refl Bool.true) (allA_succ_of_accept 52 63 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 52
  63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 115
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 51 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 115 (accept_3_3 50 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 115 (Polychromatic418967fa.accept_19_11_6_1_1_2826 49 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 115 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 115 (accept_3_3 47 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 63 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 115
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 115 (accept_3_3 44 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 115 (Polychromatic418967fa.accept_15_13_3_10_1_2296 43 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 115 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 115 (accept_3_3 41 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 115
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 115 (accept_3_3 38 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 115 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 115 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 115 (accept_3_3 35 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 63 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 115
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 115 (accept_3_3 32 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 115 (Polychromatic418967fa.accept_24_7_15_19_1_5392 31 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 115 (Polychromatic418967fa.accept_19_11_6_1_1_2826 30 63 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 115 (accept_3_3 29 63 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 115
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 115 (accept_3_3 26 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 115 (Polychromatic418967fa.accept_11_3_8_5_1_336 25 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 115 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 115 (accept_3_3 23 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 63 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 115
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 115 (accept_3_3 20 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 115 (Polychromatic418967fa.accept_25_19_13_15_1_5391 19 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 115 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 115 (accept_3_3 17 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 115
  (Polychromatic418967fa.accept_27_15_9_7_1_5390 15 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 115 (accept_3_3 14 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 115 (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 115 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 115 (accept_3_3 11 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 63 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 115
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 115 (accept_3_3 8 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  115 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 115 (Polychromatic418967fa.accept_15_6_3_10_1_2341 6 63 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 115 (accept_3_3 5 63 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 63 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 115 (Polychromatic418967fa.accept_11_3_8_5_1_336 3
  63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 115 (accept_3_3 2 63 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 115 (Polychromatic418967fa.accept_17_1_12_13_1_448
  1 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  115))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 62 115 (Eq.refl Bool.true) (allA_of_3_1 54 62
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 61 115 (Eq.refl Bool.true) (allA_succ_of_accept 54 61 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 115 (accept_3_3 53 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 115 (Polychromatic418967fa.accept_15_7_1_10_1_305 52 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 115 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 115 (accept_3_3 50 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 115 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 61 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 115
  (Polychromatic418967fa.accept_17_14_10_13_1_4147 48 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 61 115 (accept_3_3 47 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 61 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 61 115 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 61 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 115 (accept_3_3 44 61 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 115 (Polychromatic418967fa.accept_7_1_5_3_1_268 43
  61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 115 (accept_3_3 41 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 115 (Polychromatic418967fa.accept_13_1_9_11_1_703 40 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 115 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 115 (accept_3_3 38 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 115 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 61 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 115
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 115 (accept_3_3 35 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 115 (Polychromatic418967fa.accept_13_7_9_11_1_705 33 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 115 (accept_3_3 32 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 115 (Polychromatic418967fa.accept_16_15_13_3_1_4215 31 61 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 115 (accept_3_3 29 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 115 (Polychromatic418967fa.accept_13_2_9_11_1_258 28 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 115 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 115 (accept_3_3 26 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 115 (Polychromatic418967fa.accept_20_5_1_15_1_3928 25 61 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 115
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 115 (accept_3_3 23 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 115 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 61 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 115 (accept_3_3 20 61 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 115 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 61 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 115 (accept_3_3 17 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 115 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 115 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 115 (accept_3_3 14 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 115 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 61 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 115
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 115 (accept_3_3 11 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 115 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 115 (accept_3_3 8 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 115 (Polychromatic418967fa.accept_13_7_9_11_1_705 7 61 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 115 (accept_3_3 5 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  115 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 115 (Polychromatic418967fa.accept_17_3_10_13_1_2021 3 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 115 (accept_3_3 2 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 115 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 61 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  115))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 60 115 (Eq.refl Bool.true) (allA_succ_of_gcd
  55 60 115 5 11 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 60 115 (Polychromatic418967fa.accept_19_16_3_1_1_5389 54 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 115 (accept_3_3 53 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 60 115 (Polychromatic418967fa.accept_16_4_12_3_1_2180 52 60 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 60 115
  (Polychromatic418967fa.accept_21_9_18_10_1_5388 51 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 115 5 10 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 115 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 115 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 60 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 115 (accept_3_3 47 60 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 46
  60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 115 5 9 12 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 115 (accept_3_3 44
  60 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 115
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 60 115 (Polychromatic418967fa.accept_13_3_8_11_1_1906 42 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 115 (accept_3_3 41 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 60 115 5 8 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 60 115 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 60 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 115 (accept_3_3 38 60 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 60 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 115
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 60 115 5 7 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 60 115 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 60 115 (Polychromatic418967fa.accept_17_16_9_13_1_3087 33 60
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 115 (accept_3_3 32 60 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 115 (Polychromatic418967fa.accept_8_7_4_3_1_156 31
  60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 115 5 6 12 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 115 (accept_3_3 29
  60 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 115
  (Polychromatic418967fa.accept_9_1_6_7_1_285 28 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 60 115 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 115 (accept_3_3 26 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 60 115 5 5 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 60 115 (Polychromatic418967fa.accept_16_8_12_3_1_4194 24 60 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 115 (accept_3_3 23 60 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 115 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 60 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 60 115
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 115 5 4 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 115 (Polychromatic418967fa.accept_22_18_16_5_1_5387 18 60
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 115 (accept_3_3 17 60 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 115 (Polychromatic418967fa.accept_13_3_8_11_1_1906
  16 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 115 5 3 12 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 115 (accept_3_3 14
  60 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 115
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 60 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 115 (accept_3_3 11 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 60 115 5 2 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 60 115 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 60 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 115 (accept_3_3 8 60 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 115 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 60 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 115
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 60 115 5 1 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 60 115 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 60 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 115 (accept_3_3 2 60 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 115 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 60
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  115)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 59 115 (Eq.refl Bool.true) (allA_of_3_1 57
  59 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 115 (allA_succ_of_accept 57 58 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 58 115 (accept_3_3 56 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  58 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 58 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 115 (accept_3_3 53 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 115 (Polychromatic418967fa.accept_10_2_8_5_1_587 52 58 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 58 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 58 115 (accept_3_3 50 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  58 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 58 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 115 (accept_3_3 47 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 58 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 115 (accept_3_3 44 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 115 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 115 (accept_3_3 41 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 58 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 115 (accept_3_3 38 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 115 (accept_3_3 35 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 58 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 115 (accept_3_3 32 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 115 (Polychromatic418967fa.accept_13_5_6_11_1_1933 31 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 115 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 115 (accept_3_3 29 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 58 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 115 (accept_3_3 26 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 115 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 115 (accept_3_3 23 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 58 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 115 (accept_3_3 20 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 115 (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 58 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 115 (accept_3_3 17 58 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 115 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 58 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 115 (accept_3_3 14 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 115 (accept_3_3 11 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 58 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 115 (accept_3_3 8 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  115 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 58 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 115 (accept_3_3 5 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 58 115 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 58 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 58 115 (accept_3_3 2 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58
  115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 115)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 115 (allA_succ_of_accept 56
  57 115 (accept_3_3 56 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 115
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 115 (accept_3_3 53 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 115 (Polychromatic418967fa.accept_7_2_1_3_1_102 51
  57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 115 (accept_3_3 50 57
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 115
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 57 115 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 115 (accept_3_3 47 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 115 (Polychromatic418967fa.accept_13_6_5_11_1_1971
  45 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 115 (accept_3_3 44
  57 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 115
  (Polychromatic418967fa.accept_10_3_7_5_1_288 43 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 115 (accept_3_3 41 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 115 (Polychromatic418967fa.accept_7_4_1_3_1_277 39
  57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 115 (accept_3_3 38 57
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 115
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 57 115 (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 115 (accept_3_3 35 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 57 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 33
  57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 115 (accept_3_3 32 57
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 115
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 57 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 115 (accept_3_3 29 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 57 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 115 (Polychromatic418967fa.accept_12_3_9_7_1_472
  27 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 115 (accept_3_3 26
  57 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 115
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 115 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 115 (accept_3_3 23 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 115
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 57 115 (accept_3_3 20 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  57 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 57 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 115 (accept_3_3 17 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 115
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 115 (accept_3_3 14 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  57 115 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 57 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 115 (accept_3_3 11 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 115
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 57 115 (accept_3_3 8 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57
  115 (Polychromatic418967fa.accept_13_7_5_11_1_1927 7 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 57 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 115 (accept_3_3 5 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 115
  (Polychromatic418967fa.accept_10_3_7_5_1_288 3 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 57 115 (accept_3_3 2 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57
  115 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 57 115))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 115 (allA_of_3_1 56 56 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 115 (allA_succ_of_accept 54 55 115
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 54 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 115 (accept_3_3 53 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 115 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 115 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 55 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 55 115 5 10 11 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 55 115
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 115 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 115 (accept_3_3 47 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 115 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 55 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 55 115 5 9 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 55 115 (accept_3_3 44 55 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 115 (Polychromatic418967fa.accept_16_11_7_3_1_3163 43 55 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 115
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 115 (accept_3_3 41 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 55
  115 5 8 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  55 115 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 55 115 (accept_3_3 38 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 55 115 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 115 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 55 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 55 115 5 7 11 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 55 115
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 34 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 55 115 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 115 (accept_3_3 32 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 55 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 55 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 55 115 5 6 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 55 115 (accept_3_3 29 55 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 115 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 55 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 115
  (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 115 (accept_3_3 26 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55
  115 5 5 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  55 115 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 55 115 (accept_3_3 23 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 55 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 115 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 55 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 55 115 5 4 11 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 55 115
  (Polychromatic418967fa.accept_25_19_5_15_1_5386 19 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 115 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 115 (accept_3_3 17 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 115 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 55 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 115 5 3 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 115 (accept_3_3 14 55 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 55 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 115
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 115 (accept_3_3 11 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55
  115 5 2 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  55 115 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 55 115 (accept_3_3 8 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 55 115 (Polychromatic418967fa.accept_13_7_3_11_1_280 7 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 115 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 55 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 55 115 5 1 11 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 55 115
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 115 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 115 (accept_3_3 2 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 115 (Polychromatic418967fa.accept_13_1_3_11_1_1289 1 55 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 115)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 115 (allA_succ_of_accept 53 54 115 (accept_3_3 53 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 115 (Polychromatic418967fa.accept_16_4_6_3_1_1311 52 54 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 54 115 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 54 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 115 (accept_3_3 50 54 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 115
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 48 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 115 (accept_3_3 47 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 115 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 115 (accept_3_3 44 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 115 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 54 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 115
  (Polychromatic418967fa.accept_13_3_2_11_1_1999 42 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 115 (accept_3_3 41 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 115 (Polychromatic418967fa.accept_21_19_12_10_1_5385 40 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 115 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 115 (accept_3_3 38 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 115
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 115 (accept_3_3 35 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 115 (Polychromatic418967fa.accept_15_4_9_10_1_5384 34 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 115 (accept_3_3 32 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 115 (Polychromatic418967fa.accept_10_1_4_5_1_1031 31 54 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 115
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 115 (accept_3_3 29 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 115 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 115 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 54 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 115 (accept_3_3 26 54 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 115
  (Polychromatic418967fa.accept_19_5_16_1_1_2783 24 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 115 (accept_3_3 23 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 115 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 115 (accept_3_3 20 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 115 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 54 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 115
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 18 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 115 (accept_3_3 17 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 115 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 115 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 115 (accept_3_3 14 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 115
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 115 (accept_3_3 11 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 115 (Polychromatic418967fa.accept_13_10_2_11_1_1920 10 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 115 (accept_3_3 8 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 115 (Polychromatic418967fa.accept_31_7_23_22_1_5383 7 54 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 115
  (Polychromatic418967fa.accept_10_6_4_5_1_615 6 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 115 (accept_3_3 5 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  115 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 115 (Polychromatic418967fa.accept_13_3_2_11_1_1999 3 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 115 (accept_3_3 2 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  115)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 115 (allA_of_3_1 53 53 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 115 (allA_succ_of_accept 51 52 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 115 (accept_3_3 50 52 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 115 (Polychromatic418967fa.accept_14_7_10_3_1_1034
  49 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 115
  (Polychromatic418967fa.accept_10_8_2_5_1_596 48 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 115 (accept_3_3 47 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 115 (Polychromatic418967fa.accept_11_2_8_5_1_1219 46 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 115 (accept_3_3 44 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 115 (Polychromatic418967fa.accept_10_3_2_5_1_295 43 52 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 115
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 42 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 115 (accept_3_3 41 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 115 (Polychromatic418967fa.accept_16_8_4_3_1_3146 40 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 115 (accept_3_3 38 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 115 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 52 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 115
  (Polychromatic418967fa.accept_11_3_8_5_1_336 36 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 115 (accept_3_3 35 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 115 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 115 (accept_3_3 32 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 115 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 52 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 115
  (Polychromatic418967fa.accept_20_10_12_15_1_3940 30 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 52 115 (accept_3_3 29 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 52 115 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 52 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 115 (accept_3_3 26 52 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 115 (Polychromatic418967fa.accept_11_3_8_5_1_336
  25 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 115
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 115 (accept_3_3 23 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 115 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 115 (accept_3_3 20 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 115 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 52 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 115
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 115 (accept_3_3 17 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 115 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 115 (accept_3_3 14 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 115 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 52 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 115
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 12 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 115 (accept_3_3 11 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 115 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 115 (accept_3_3 8 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 115 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 52 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 115
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 115 (accept_3_3 5 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  115 (Polychromatic418967fa.accept_15_4_7_10_1_807 4 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 52 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 115 (accept_3_3 2 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 115 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 52 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  115)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 115 (allA_succ_of_accept 50 51 115 (accept_3_3
  50 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 115
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 115 (accept_3_3 47 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 51 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 115 (Polychromatic418967fa.accept_12_9_3_7_1_924
  45 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 115 (accept_3_3 44
  51 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 115
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 51 115 (Polychromatic418967fa.accept_11_9_7_5_1_749 42 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 115 (accept_3_3 41 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 51 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 39
  51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 115 (accept_3_3 38 51
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 115
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 51 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 115 (accept_3_3 35 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 51 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 51 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 33
  51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 115 (accept_3_3 32 51
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 115
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 51 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 115 (accept_3_3 29 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 51 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 27
  51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 115 (accept_3_3 26 51
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 115
  (Polychromatic418967fa.accept_20_5_11_15_1_3920 25 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 51 115 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 115 (accept_3_3 23 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 51 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 51 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 21
  51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 115 (accept_3_3 20 51
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 115
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 51 115 (Polychromatic418967fa.accept_15_3_6_10_1_1539 18 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 115 (accept_3_3 17 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 51 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 15
  51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 115 (accept_3_3 14 51
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 115
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 51 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 115 (accept_3_3 11 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 51 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 51 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 115 (Polychromatic418967fa.accept_10_9_1_5_1_594 9
  51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 115 (accept_3_3 8 51 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 115 (Polychromatic418967fa.accept_13_7_12_11_1_1911
  7 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 115
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 115 (accept_3_3 5 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 115 (accept_3_3 2 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 51 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 115)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 115 (allA_of_3_1 50 50 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 115
  (allA_succ_of_accept 48 49 115 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 49 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 115 (accept_3_3 47 49 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 115 (Polychromatic418967fa.accept_16_13_1_3_1_2205
  45 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 115 (accept_3_3 44
  49 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 115
  (Polychromatic418967fa.accept_13_4_10_11_1_1908 43 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 49 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 115 (accept_3_3 41 49 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 49 115 (Polychromatic418967fa.accept_13_1_10_11_1_1280 40 49 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 115
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 115 (accept_3_3 38 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 115 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 49 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 115 (accept_3_3 35 49 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 115
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 115 (accept_3_3 32 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 115 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 115 (accept_3_3 29 49 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 49 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 115
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 115 (accept_3_3 26 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 115 (Polychromatic418967fa.accept_13_12_10_11_1_1279 25 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 115 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 49 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 115 (accept_3_3 23 49 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 115
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 115 (accept_3_3 20 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 115 (accept_3_3 17 49 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 115 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 49 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 115
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 115 (accept_3_3 14 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 115 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 115 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 49 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 115 (accept_3_3 11 49 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 115
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 115 (accept_3_3 8 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  115 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 49 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 115 (accept_3_3 5 49 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 115 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 49 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 115
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 115 (accept_3_3 2 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  115 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 49 115))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 115 (allA_succ_of_accept 47 48 115
  (accept_3_3 47 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 115
  (Polychromatic418967fa.accept_7_4_6_3_1_271 46 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 48 115 (Polychromatic418967fa.accept_19_7_10_1_1_5382 45 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 115 (accept_3_3 44 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 48 115 (Polychromatic418967fa.accept_10_3_8_5_1_606 43 48 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 115 (Polychromatic418967fa.accept_9_6_3_7_1_580 42
  48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 115 (accept_3_3 41 48
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 115
  (Polychromatic418967fa.accept_9_4_3_7_1_296 40 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 48 115 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 115 (accept_3_3 38 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 48 115 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 48 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 115 (Polychromatic418967fa.accept_15_6_3_10_1_2341
  36 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 115 (accept_3_3 35
  48 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 115
  (Polychromatic418967fa.accept_13_8_9_11_1_1265 34 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 48 115 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 115 (accept_3_3 32 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 48 115 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 48 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 115 (Polychromatic418967fa.accept_7_2_6_3_1_100 30
  48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 115 (accept_3_3 29 48
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 115 (Polychromatic418967fa.accept_9_1_3_7_1_6
  28 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 48 115
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 48 115 (accept_3_3 26 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  48 115 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 48 115 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 48 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 115 (accept_3_3 23 48 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 115 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 48 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 48 115
  (Polychromatic418967fa.accept_11_10_4_5_1_359 21 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 48 115 (accept_3_3 20 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  48 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 48 115 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 48 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 115 (accept_3_3 17 48 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 115 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 48 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 48 115
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 48 115 (accept_3_3 14 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  48 115 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 48 115 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 48 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 115 (accept_3_3 11 48 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 48 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 48 115
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 48 115 (accept_3_3 8 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48
  115 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 48 115 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 48 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 115 (accept_3_3 5 48 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 115 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 48 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48 115
  (Polychromatic418967fa.accept_10_3_8_5_1_606 3 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 115 (accept_3_3 2 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48
  115 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 115)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 115 (allA_of_3_1 47 47 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 46 115 (allA_succ_of_accept 45 46 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 115 (accept_3_3 44 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 115 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 115 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 46 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 115 (accept_3_3 41 46 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 46 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 115 (accept_3_3 38 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 115 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 46 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 115 (accept_3_3 35 46 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 115 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 46 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 115 (accept_3_3 32 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 115 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 46 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 115 (accept_3_3 29 46 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 115 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 46 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 115 (accept_3_3 26 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 115 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 46 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 23 46 115 23 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 22 46 115 (Polychromatic418967fa.accept_7_1_4_3_1_21 22
  46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 115 (accept_3_3 20 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 115 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 115 (Polychromatic418967fa.accept_13_5_7_11_1_3470 18 46 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 115 (accept_3_3 17 46 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 115 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 46 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 115 (accept_3_3 14 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 115 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 46 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 115 (accept_3_3 11 46 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 115 (Polychromatic418967fa.accept_20_10_6_15_1_5381 10 46 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 115 (accept_3_3 8 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  115 (Polychromatic418967fa.accept_14_7_4_3_1_488 7 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 115 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 46 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 115 (accept_3_3 5 46 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 46 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 46
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 115 (accept_3_3 2 46 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  115)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 115 (allA_succ_of_accept 44 45 115 (accept_3_3 44 45
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 115
  (Polychromatic418967fa.accept_13_4_6_11_1_2017 43 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 115 (accept_3_3 41 45 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 45 115 5 8 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 45 115 (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 45 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 115 (accept_3_3 38 45 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 115 (Polychromatic418967fa.accept_19_18_7_1_1_2770 37 45 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 115
  (Polychromatic418967fa.accept_20_16_5_15_1_5364 36 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 45 115 5 7 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 45 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 115 (Polychromatic418967fa.accept_16_1_13_3_1_2168 33 45
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 115 (accept_3_3 32 45 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 115 (Polychromatic418967fa.accept_13_5_6_11_1_1933
  31 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 115 5 6 9 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 115 (accept_3_3 29
  45 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 115
  (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 45 115 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 45 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 115 (accept_3_3 26 45 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 45 115 5 5 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 45 115 (Polychromatic418967fa.accept_16_8_13_3_1_4253 24 45 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 115 (accept_3_3 23 45 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 115
  (Polychromatic418967fa.accept_13_8_6_11_1_1979 21 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 45 115 5 4 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 45 115 (Polychromatic418967fa.accept_20_19_5_15_1_5380 19 45 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 115 (accept_3_3 17 45 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 115 5 3 9 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 115 (accept_3_3 14
  45 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 115
  (Polychromatic418967fa.accept_19_13_7_1_1_5379 13 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 45 115 (Polychromatic418967fa.accept_17_12_11_13_1_5378 12 45 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 115 (accept_3_3 11 45 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 45 115 5 2 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 45 115 (Polychromatic418967fa.accept_20_9_5_15_1_3965 9 45 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 115 (accept_3_3 8 45 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 115 (Polychromatic418967fa.accept_17_7_11_13_1_2037 7 45 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 45 115 5 1 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 45 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 115 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 45 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 115 (accept_3_3 2 45 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 115 (Polychromatic418967fa.accept_16_1_13_3_1_2168
  1 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  115))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 115 (allA_of_3_1 44 44 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 43 115 (allA_succ_of_accept 42 43 115 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 43 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 115 (accept_3_3 41 43 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 40
  43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 115
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 115 (accept_3_3 38 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 115 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 115 (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 43 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 115 (accept_3_3 35 43 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 115 (Polychromatic418967fa.accept_13_8_4_11_1_3469 34 43
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 115
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 115 (accept_3_3 32 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 115 (Polychromatic418967fa.accept_15_1_13_10_1_1507 31 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 115 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 43 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 115 (accept_3_3 29 43 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 115 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 43 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 115
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 115 (accept_3_3 26 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 115 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 115 (Polychromatic418967fa.accept_16_8_11_3_1_4279 24 43 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 115 (accept_3_3 23 43 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 115 (Polychromatic418967fa.accept_10_2_3_5_1_996 22 43 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 115
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 115 (accept_3_3 20 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 115 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 43 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 115 (accept_3_3 17 43 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 115 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 43 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 115
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 115 (accept_3_3 14 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 115 (Polychromatic418967fa.accept_21_13_1_10_1_5377 13 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 43 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 115 (accept_3_3 11 43 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 115 (Polychromatic418967fa.accept_13_10_4_11_1_1969 10 43 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 115
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 115 (accept_3_3 8 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  115 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 115 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 43 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 115 (accept_3_3 5 43 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 115 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 43 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 115 (Polychromatic418967fa.accept_15_3_13_10_1_2332
  3 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 115 (accept_3_3 2 43
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 115
  (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 43 115))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 115 (allA_succ_of_accept 41 42 115
  (accept_3_3 41 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 115
  (Polychromatic418967fa.accept_9_4_6_7_1_286 40 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 42 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 42 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 115 (accept_3_3 38 42 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 42 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 115
  (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 115 (accept_3_3 35 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 115 (Polychromatic418967fa.accept_13_8_3_11_1_3467 34 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 115 (accept_3_3 32 42 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 115 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 42 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 115
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 115 (accept_3_3 29 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 115 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 42 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 115 (accept_3_3 26 42 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 115
  (Polychromatic418967fa.accept_15_9_12_10_1_809 24 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 115 (accept_3_3 23 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 115 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 115 (accept_3_3 20 42 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 42 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 115
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 115 (accept_3_3 17 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 115 (Polychromatic418967fa.accept_19_16_4_1_1_5376 16 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 115 (Polychromatic418967fa.accept_13_2_3_11_1_1287 15 42 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 115 (accept_3_3 14 42 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 115
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 115 (accept_3_3 11 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 115 (accept_3_3 8 42 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 115 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 42 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 115
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 6 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 115 (accept_3_3 5 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  115 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 42 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 115 (accept_3_3 2 42 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 115)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 115
  (allA_of_3_1 41 41 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 115 (allA_succ_of_accept 39 40 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 115 (accept_3_3 38 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 115 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 115 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 40 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 40 115 5 7 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 40 115 (Polychromatic418967fa.accept_12_10_4_7_1_948
  34 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 115 (accept_3_3 32 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 115 (Polychromatic418967fa.accept_11_9_7_5_1_749 31 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 40 115 5 6 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 40 115 (accept_3_3 29 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 40 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 40 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 115 (accept_3_3 26 40 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 40 115 5 5 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 40 115 (Polychromatic418967fa.accept_9_6_4_7_1_300 24
  40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 115 (accept_3_3 23 40
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 115
  (Polychromatic418967fa.accept_7_1_5_3_1_268 22 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 40 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 115 5 4 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 40 115
  (Polychromatic418967fa.accept_19_18_2_1_1_5375 18 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 40 115 (accept_3_3 17 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  40 115 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 40 115 5 3 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 40 115 (accept_3_3 14 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 40 115 (Polychromatic418967fa.accept_16_13_8_3_1_5374 13 40 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 115 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 40 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 115 (accept_3_3 11 40 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 115 5 2 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 40 115 (accept_3_3 8 40 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40 115 (Polychromatic418967fa.accept_13_7_1_11_1_732 7
  40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 40 115
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 40 115 5 1 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 40 115 (Polychromatic418967fa.accept_16_4_8_3_1_4206 4 40 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 115 (accept_3_3 2 40 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 115 (Polychromatic418967fa.accept_7_1_5_3_1_268 1
  40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  115)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 115 (allA_succ_of_accept 38 39 115 (accept_3_3 38 39 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 37
  39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 115
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 115 (accept_3_3 35 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  39 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 115 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 39 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 115 (accept_3_3 32 39 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 115 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 39 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 115
  (Polychromatic418967fa.accept_18_12_3_7_1_5373 30 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 115 (accept_3_3 29 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 115 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 39 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 115 (accept_3_3 26 39 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 115 (Polychromatic418967fa.accept_16_9_7_3_1_614 25 39 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 115
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 115 (accept_3_3 23 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 115 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 39 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 115 (accept_3_3 20 39 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 39 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 115
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 18 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 115 (accept_3_3 17 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 115 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 39 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 115 (accept_3_3 14 39 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 115 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 39 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 115
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 115 (accept_3_3 11 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 115 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 39 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 115 (accept_3_3 8 39 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 115 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 39 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 115
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 115 (accept_3_3 5 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 115 (Polychromatic418967fa.accept_15_3_9_10_1_2325 3 39 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 115 (accept_3_3 2 39 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 115 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 39 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 115))))))))))))))))))))))))))))))))))))))) (allB_succ 38 115
  (allA_of_3_1 38 38 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 115 (allA_succ_of_accept 36 37 115
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 115 (accept_3_3 35 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 37 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 115 (accept_3_3 32 37 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 37 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 115 (accept_3_3 29 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 115 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 37 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 115 (accept_3_3 26 37 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 115 (Polychromatic418967fa.accept_17_8_3_13_1_5372 25 37 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 115
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 115 (accept_3_3 23 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 115 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 37 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 115 (accept_3_3 20 37 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 37 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 115 (accept_3_3 17 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 115 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 37 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 115 (accept_3_3 14 37 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 37 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 115
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 115 (accept_3_3 11 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 115 (Polychromatic418967fa.accept_21_9_16_10_1_5371 9 37 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 115 (accept_3_3 8 37 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 115 (Polychromatic418967fa.accept_19_7_18_1_1_1662 7 37 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 115 (accept_3_3 5 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  115 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 115 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 37 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 115 (accept_3_3 2 37 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 37 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 115))))))))))))))))))))))))))))))))))))) (allB_succ 36 115
  (allA_succ_of_accept 35 36 115 (accept_3_3 35 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  36 115 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 36 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 36 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 115 (accept_3_3 32 36 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 115 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 36 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 115
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 115 (accept_3_3 29 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 115 (Polychromatic418967fa.accept_13_2_10_11_1_1276 28 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 115 (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 36 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 115 (accept_3_3 26 36 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 115 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 36 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 115
  (Polychromatic418967fa.accept_10_4_6_5_1_74 24 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 115 (accept_3_3 23 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  36 115 (Polychromatic418967fa.accept_16_6_4_3_1_2189 22 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 115 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 36 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 115 (accept_3_3 20 36 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 36 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 115
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 36 115 (accept_3_3 17 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  36 115 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 36 115 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 36 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 115 (accept_3_3 14 36 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 115 (Polychromatic418967fa.accept_22_13_14_5_1_5370 13 36 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 115
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 115 (accept_3_3 11 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 115 (Polychromatic418967fa.accept_19_10_17_1_1_4010 10 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 115 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 36 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 115 (accept_3_3 8 36 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 115 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 36 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 115
  (Polychromatic418967fa.accept_16_6_4_3_1_2189 6 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 115 (accept_3_3 5 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  115 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 36 115 (Polychromatic418967fa.accept_13_3_10_11_1_1293 3 36 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 115 (accept_3_3 2 36 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 36 115 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 36 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 115)))))))))))))))))))))))))))))))))))) (allB_succ 35 115
  (allA_of_3_1 35 35 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 115 (allA_succ_of_accept 33 34 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 115 (accept_3_3 32 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 115 (Polychromatic418967fa.accept_10_1_4_5_1_1031 31 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 115 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 34 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 115 (accept_3_3 29 34 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 115 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 34 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 115 (accept_3_3 26 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 115 (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 34 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 115 (accept_3_3 23 34 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 115 (Polychromatic418967fa.accept_13_9_8_11_1_725 22 34 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 115 (accept_3_3 20 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 115 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 115 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 34 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 115 (accept_3_3 17 34 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 115 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 34 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 115 (accept_3_3 14 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 115 (Polychromatic418967fa.accept_31_12_3_22_1_5369 12 34 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 115 (accept_3_3 11 34 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 115 (Polychromatic418967fa.accept_13_10_8_11_1_1985 10 34
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 115 (accept_3_3 8 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  115 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 34 115 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 34 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 115 (accept_3_3 5 34 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 34 115 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 34 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 34 115 (accept_3_3 2 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34
  115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 115)))))))))))))))))))))))))))))))))) (allB_succ 33 115 (allA_succ_of_accept 32 33 115 (accept_3_3 32 33
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 115
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 33 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 115 (accept_3_3 29 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 33 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 33 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 115 (Polychromatic418967fa.accept_10_7_3_5_1_301
  27 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 115 (accept_3_3 26
  33 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 115
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 25 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 33 115 (Polychromatic418967fa.accept_15_9_3_10_1_2312 24 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 115 (accept_3_3 23 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 33 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 21
  33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 115 (accept_3_3 20 33
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 115
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 33 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 115 (accept_3_3 17 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 33 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 115 (Polychromatic418967fa.accept_7_1_5_3_1_268 15
  33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 115 (accept_3_3 14 33
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 115
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 33 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 115 (accept_3_3 11 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 33 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 115 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 33
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 115 (accept_3_3 8 33 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 115 (Polychromatic418967fa.accept_10_7_3_5_1_301 7
  33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 115 (accept_3_3 5 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 115 (accept_3_3 2 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 115 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 33 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 115))))))))))))))))))))))))))))))))) (allB_succ 32 115
  (allA_of_3_1 32 32 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 115 (allA_succ_of_accept 30 31 115
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 115 (accept_3_3 29 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 115 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 115 (Polychromatic418967fa.accept_16_11_15_3_1_1304 27 31 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 115 (accept_3_3 26 31 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 115 (Polychromatic418967fa.accept_20_5_11_15_1_3920 25 31
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 115
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 115 (accept_3_3 23 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 115 (Polychromatic418967fa.accept_15_7_1_10_1_305 22 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 115 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 31 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 115 (accept_3_3 20 31 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 31 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 115
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 115 (accept_3_3 17 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 115 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 115 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 31 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 115 (accept_3_3 14 31 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 115 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 31 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 115
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 115 (accept_3_3 11 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 115 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 31 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 115 (accept_3_3 8 31 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 115 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 31 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 115
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 115 (accept_3_3 5 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  115 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 115 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 31 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 115 (accept_3_3 2 31 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 31 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 115))))))))))))))))))))))))))))))) (allB_succ 30 115
  (allA_succ_of_accept 29 30 115 (accept_3_3 29 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  30 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 30 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 30 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 115 (accept_3_3 26 30 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 25 30 115 5 5 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 30 115 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 30 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 115 (accept_3_3 23 30 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 30 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 30 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 115 5 4 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 30 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 115 (Polychromatic418967fa.accept_19_18_11_1_1_4035 18 30
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 115 (accept_3_3 17 30 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 115
  (Polychromatic418967fa.accept_20_16_10_15_1_5368 16 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 30 115 5 3 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 30 115 (accept_3_3 14 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 30 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 115 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 30 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 115 (accept_3_3 11 30 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 115 5 2 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 115 (accept_3_3 8 30 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 115 (Polychromatic418967fa.accept_13_7_4_11_1_1967
  7 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 115
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 30 115 5 1 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 30 115 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 30 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 115 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 30 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 115 (accept_3_3 2 30 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 115))))))))))))))))))))))))))))))
  (allB_succ 29 115 (allA_of_3_1 29 29 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 115
  (allA_succ_of_accept 27 28 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 28 115 (accept_3_3 26 28 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 28 115 (Polychromatic418967fa.accept_16_9_12_3_1_3138 25 28 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 28 115
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 28 115 (accept_3_3 23 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  28 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 28 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 28 115 (accept_3_3 20 28 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 28 115 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 28 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 115
  (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 28 115 (accept_3_3 17 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  28 115 (Polychromatic418967fa.accept_13_3_2_11_1_1999 16 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 28 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 28 115 (accept_3_3 14 28 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 28 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 28 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 115
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 28 115 (accept_3_3 11 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  28 115 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 28 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 115 (accept_3_3 8 28 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 28 115 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 28 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 115
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 28 115 (accept_3_3 5 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28
  115 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 28 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 115 (accept_3_3 2 28 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 28 115 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 28 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 115)))))))))))))))))))))))))))) (allB_succ 27 115
  (allA_succ_of_accept 26 27 115 (accept_3_3 26 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  27 115 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 27 115 (Polychromatic418967fa.accept_14_10_13_3_1_2552 24 27 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 115 (accept_3_3 23 27 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 27 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 115
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 115 (accept_3_3 20 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 115 (Polychromatic418967fa.accept_29_19_27_28_1_5367 19 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 115 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 27 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 115 (accept_3_3 17 27 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 115
  (Polychromatic418967fa.accept_16_15_11_3_1_2179 15 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 115 (accept_3_3 14 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 115 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 115 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 27 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 115 (accept_3_3 11 27 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 27 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 115
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 115 (accept_3_3 8 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  115 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 115 (Polychromatic418967fa.accept_15_6_12_10_1_1543 6 27 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 115 (accept_3_3 5 27 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 115
  (Polychromatic418967fa.accept_10_3_7_5_1_288 3 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 115 (accept_3_3 2 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  115 (Polychromatic418967fa.accept_20_1_7_15_1_1521 1 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 115))))))))))))))))))))))))))) (allB_succ 26 115 (allA_of_3_1 26 26 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 25 115 (allA_succ_of_accept 24 25 115 (Polychromatic418967fa.accept_19_5_6_1_1_5366 24
  25 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 115 (accept_3_3 23 25
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 115 (Polychromatic418967fa.accept_4_2_1_3_1_27
  22 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 115
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 21 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 25 115 5 4 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 25 115 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 25 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 115 (accept_3_3 17 25 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 115
  (Polychromatic418967fa.accept_20_16_5_15_1_5364 16 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 25 115 5 3 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 25 115 (accept_3_3 14 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 115 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 115 (Polychromatic418967fa.accept_16_12_9_3_1_5363 12 25 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 115 (accept_3_3 11 25 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25 115 5 2 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25 115 (Polychromatic418967fa.accept_20_9_5_15_1_3965 9 25 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 115 (accept_3_3 8 25 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 115 (Polychromatic418967fa.accept_13_7_12_11_1_1911
  7 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 25 115 5 1 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 25 115 (Polychromatic418967fa.accept_13_4_12_11_1_5362 4 25 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 115 (Polychromatic418967fa.accept_17_3_8_13_1_5361 3 25 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 115 (accept_3_3 2 25 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 115 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 25
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 115))))))))))))))))))))))))) (allB_succ
  24 115 (allA_succ_of_accept 23 24 115 (accept_3_3 23 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 115 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 24 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 115 (accept_3_3 20 24 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 19
  24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 115
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 18 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 24 115 (accept_3_3 17 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  24 115 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 24 115 (Polychromatic418967fa.accept_19_15_5_1_1_5360 15 24 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 115 (accept_3_3 14 24 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 115 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 24 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 115
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 24 115 (accept_3_3 11 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  24 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 24 115 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 24 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 115 (accept_3_3 8 24 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 115 (Polychromatic418967fa.accept_14_7_10_3_1_1034 7 24 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 115
  (Polychromatic418967fa.accept_10_6_4_5_1_615 6 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 115 (accept_3_3 5 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24
  115 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 24 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 115 (accept_3_3 2 24 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 24 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 24 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 115)))))))))))))))))))))))) (allB_succ 23 115 (allA_of_3_1 23 23
  115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 115 (allA_succ_of_accept 21 22 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 115 (accept_3_3 20 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 115 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 22 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 115 (accept_3_3 17 22 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 115 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 22 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 115 (accept_3_3 14 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 22 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 115 (accept_3_3 11 22 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 22 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 115 (accept_3_3 8 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  115 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 115 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 22 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 115 (accept_3_3 5 22 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 115 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 22 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 22
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 115 (accept_3_3 2 22 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 115)))))))))))))))))))))) (allB_succ 21
  115 (allA_succ_of_accept 20 21 115 (accept_3_3 20 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 21 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 21 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 115 (accept_3_3 17 21 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 115
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 115 (accept_3_3 14 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 115 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 115 (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 21 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 115 (accept_3_3 11 21 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 115
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 115 (accept_3_3 8 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  115 (Polychromatic418967fa.accept_19_7_2_1_1_4076 7 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 21 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 115 (accept_3_3 5 21 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 115
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 115 (accept_3_3 2 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21
  115 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 21 115))))))))))))))))))))) (allB_succ 20 115 (allA_of_3_1 20 20 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 19 115 (allA_succ_of_accept 18 19 115 (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 19 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 115 (accept_3_3 17 19 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 115 (Polychromatic418967fa.accept_7_2_5_3_1_98 16
  19 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 115
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 19 115 (accept_3_3 14 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  19 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 19 115 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 19 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 115 (accept_3_3 11 19 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 115 (Polychromatic418967fa.accept_20_10_19_15_1_2692 10 19 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 115
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 19 115 (accept_3_3 8 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19
  115 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 19 115 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 19 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 115 (accept_3_3 5 19 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 19 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 115
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 19 115 (accept_3_3 2 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19
  115 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 19 115))))))))))))))))))) (allB_succ 18 115 (allA_succ_of_accept 17 18 115 (accept_3_3 17 18 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 115 (Polychromatic418967fa.accept_13_3_5_11_1_716 16 18 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 115
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 18 115 (accept_3_3 14 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  18 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 18 115 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 18 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 115 (accept_3_3 11 18 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 115 (Polychromatic418967fa.accept_20_10_18_15_1_5359 10 18 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 115
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 18 115 (accept_3_3 8 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18
  115 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 18 115 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 18 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 115 (accept_3_3 5 18 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 115 (Polychromatic418967fa.accept_22_4_18_5_1_5358 4 18 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 115
  (Polychromatic418967fa.accept_10_3_8_5_1_606 3 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 18 115 (accept_3_3 2 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18
  115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 115)))))))))))))))))) (allB_succ 17 115 (allA_of_3_1 17 17 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 16 115 (allA_succ_of_accept 15 16 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 115 (accept_3_3 14 16 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 115 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 16 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 115
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 16 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 115 (accept_3_3 11 16 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  16 115 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 16 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 16 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 115 (accept_3_3 8 16 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 115 (Polychromatic418967fa.accept_13_7_3_11_1_280 7 16 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 115
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 16 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 115 (accept_3_3 5 16 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16
  115 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 16 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 16 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 115 (accept_3_3 2 16 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 16 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 16 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 115)))))))))))))))) (allB_succ 15 115 (allA_succ_of_accept 14 15
  115 (accept_3_3 14 15 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 115
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 15 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 115 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 15 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 115 (accept_3_3 11 15 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 15 115 5 2 3 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 15 115 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 15 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 115 (accept_3_3 8 15 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 115 (Polychromatic418967fa.accept_16_7_15_3_1_1302 7 15 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 115
  (Polychromatic418967fa.accept_21_6_15_10_1_2579 6 15 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 15 115 5 1 3 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 15 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 15 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 115 (accept_3_3 2 15 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 115 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  15 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 115))))))))))))))) (allB_succ 14 115
  (allA_of_3_1 14 14 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 115 (allA_succ_of_accept 12 13 115
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 13 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 115 (accept_3_3 11 13 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 115 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 13 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 115 (accept_3_3 8 13 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 115 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 13 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 115
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 115 (accept_3_3 5 13 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  115 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 13 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 115 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 13 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 115 (accept_3_3 2 13 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 115 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 13 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 115))))))))))))) (allB_succ 12 115 (allA_succ_of_accept 11 12
  115 (accept_3_3 11 12 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 115
  (Polychromatic418967fa.accept_9_1_3_7_1_6 10 12 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 12 115 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 12 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 115 (accept_3_3 8 12 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 12 115 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 12 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 115 (Polychromatic418967fa.accept_9_6_3_7_1_580 6
  12 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 115 (accept_3_3 5 12 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 115 (Polychromatic418967fa.accept_9_4_3_7_1_296 4
  12 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12 115
  (Polychromatic418967fa.accept_10_3_2_5_1_295 3 12 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 115 (accept_3_3 2 12 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12
  115 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 12 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 115)))))))))))) (allB_succ 11 115 (allA_of_3_1 11 11 115 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 115 (allA_succ_of_accept 9 10 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 115 (accept_3_3 8 10 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 115 (Polychromatic418967fa.accept_14_7_10_3_1_1034 7 10 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 115
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 10 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 10 115 5 1 2 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 10 115 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 10 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 115 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 10 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 115 (accept_3_3 2 10 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 115)))))))))) (allB_succ 9 115
  (allA_succ_of_accept 8 9 115 (accept_3_3 8 9 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 115
  (Polychromatic418967fa.accept_11_7_9_5_1_338 7 9 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 115 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 115 (accept_3_3 5 9 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 115 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 115 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 9
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 115 (accept_3_3 2 9 115
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 115 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 9
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 115))))))))) (allB_succ 8 115
  (allA_of_3_1 8 8 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 115 (allA_succ_of_accept 6 7 115
  (Polychromatic418967fa.accept_17_6_7_13_1_3062 6 7 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 115 (accept_3_3 5 7 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 115
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 7 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 115 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 7 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 115 (accept_3_3 2 7 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 115 (Polychromatic418967fa.accept_13_1_7_11_1_702 1 7 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 115))))))) (allB_succ 6 115 (allA_succ_of_accept 5 6 115
  (accept_3_3 5 6 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 115
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 6 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 115 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 6 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 115 (accept_3_3 2 6 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 115 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 115)))))) (allB_succ 5 115 (allA_of_3_1 5 5 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 115 (allA_succ_of_accept 3 4 115
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 115 (accept_3_3 2 4 115 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 115
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 4 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 115)))) (allB_succ 3 115 (allA_succ_of_accept 2 3 115 (accept_3_3 2 3 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 115 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 3 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 115))) (allB_succ 2 115 (allA_of_3_1 2 2 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  115)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


