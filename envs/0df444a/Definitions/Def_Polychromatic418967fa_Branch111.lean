-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch111
-- name    : Polychromatic418967fa_Branch111
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:11:15.030663+00:00
-- url     : https://prove2.me/theorems/321bcabd-ef14-4d22-bb22-59e7b80d72ea
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

def Polychromatic418967fa.branch_111 : allB 111 111 :=
  allB_succ' 2 110 111 (Eq.refl Bool.true) (allA_succ_of_accept 1 110 111 (accept_3_4 1 110 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110 111)) (allB_succ' 3 109 111 (Eq.refl Bool.true) (allA_succ_of_accept 2 109 111
  (accept_3_5 2 109 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 111
  (Polychromatic418967fa.accept_25_1_9_11_1_5135 1 109 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 109 111))) (allB_succ' 4 108 111 (Eq.refl Bool.true) (allA_succ_of_gcd 3 108 111 3 1 36 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 108 111
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 108 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 108 111 (Polychromatic418967fa.accept_15_1_3_6_1_621 1 108 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108 111)))) (allB_succ' 5 107 111 (Eq.refl Bool.true) (allA_succ_of_accept 4
  107 111 (accept_3_4 4 107 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 111
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 107 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 107 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 107 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 111 (accept_3_4 1 107 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 107 111))))) (allB_succ' 6 106 111 (Eq.refl Bool.true) (allA_succ_of_accept 5 106 111
  (accept_3_5 5 106 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 106 111
  (Polychromatic418967fa.accept_9_4_7_3_1_43 4 106 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 106 111 (Polychromatic418967fa.accept_15_3_1_6_1_206 3 106 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 111 (accept_3_5 2 106 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 106 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 111)))))) (allB_succ' 7 105 111 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 105 111 3 2 35 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 105 111 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 105 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 105 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 111 3 1 35 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 105 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 105 111))))))) (allB_succ' 8 104 111 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 104 111 (accept_3_4 7 104 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 104 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 104 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 111 (accept_3_4 4 104 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 111 (Polychromatic418967fa.accept_21_3_20_6_1_5126 3 104 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 111
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 104 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 111 (accept_3_4 1 104 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  111)))))))) (allB_succ' 9 103 111 (Eq.refl Bool.true) (allA_succ_of_accept 8 103 111 (accept_3_5 8 103 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 111 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 103 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 111
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 103 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 111 (accept_3_5 5 103 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 103 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 111 (Polychromatic418967fa.accept_16_3_7_15_1_1130 3 103 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 111 (accept_3_5 2 103 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 103 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103 111))))))))) (allB_succ' 10 102 111
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 102 111 3 3 34 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 8 102 111 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 102 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 111
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 102 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 102 111 3 2 34 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 102 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 111 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 102 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 102 111 3 1 34 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 102 111
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 102 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 102 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 102 111)))))))))) (allB_succ' 11 101 111 (Eq.refl Bool.true)
  (allA_succ_of_accept 10 101 111 (accept_3_4 10 101 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  101 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 101 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 101 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 101 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 111 (accept_3_4 7 101 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 101 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 111
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 101 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 111 (accept_3_4 4 101 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 111 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 101 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 111 (accept_3_4 1 101 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101 111))))))))))) (allB_succ' 12 100 111 (Eq.refl Bool.true) (allA_succ_of_accept 11
  100 111 (accept_3_5 11 100 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 100 111
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 100 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 100 111 (Polychromatic418967fa.accept_21_9_16_6_1_5134 9 100 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 100 111 (accept_3_5 8 100 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 100 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 100 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 6
  100 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 111 (accept_3_5 5 100
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 100 111
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 100 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 100 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 100 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 111 (accept_3_5 2 100 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 100 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 100 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 111)))))))))))) (allB_succ' 13 99 111 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 99 111 3 4 33 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 99 111 (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 99 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 111 (Polychromatic418967fa.accept_13_10_8_7_1_1074 10 99
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 111 3 3 33 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 111
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 99 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 111 (Polychromatic418967fa.accept_14_7_1_13_1_357 7 99 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 99 111 3 2 33 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 99 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 99 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 111
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 99 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 99 111 3 1 33 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 99 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 99 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 111 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 99 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 111))))))))))))) (allB_succ' 14 98 111
  (Eq.refl Bool.true) (allA_succ_of_accept 13 98 111 (accept_3_4 13 98 111 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 98 111 (Polychromatic418967fa.accept_16_12_2_15_1_490 12 98 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 98 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 98 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 111 (accept_3_4 10 98 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 111
  (Polychromatic418967fa.accept_20_8_18_11_1_5133 8 98 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 111 (accept_3_4 7 98 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  111 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 98 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 111 (accept_3_4 4 98 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 111 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 98 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 111 (Polychromatic418967fa.accept_9_2_8_3_1_181 2
  98 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 111 (accept_3_4 1 98 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98 111)))))))))))))) (allB_succ' 15 97 111 (Eq.refl Bool.true)
  (allA_succ_of_accept 14 97 111 (accept_3_5 14 97 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 111 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 97 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 111 (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 97 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 111 (accept_3_5 11 97 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 111
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 97 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 111 (accept_3_5 8 97 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  111 (Polychromatic418967fa.accept_19_7_2_16_1_1496 7 97 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 111 (accept_3_5 5 97 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 111
  (Polychromatic418967fa.accept_19_3_2_16_1_5132 3 97 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 111 (accept_3_5 2 97 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  111 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 97 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 111))))))))))))))) (allB_succ' 16 96 111 (Eq.refl Bool.true) (allA_succ_of_gcd 15 96 111 3 5 32 37
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 96 111
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 96 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 96 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 96 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 111 3 4 32 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 96 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 111
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 96 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 96 111 3 3 32 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 96 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 96 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 111 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 96 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 111 3 2 32 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 111
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 96 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 96 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 96 111 3 1 32 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 96 111 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 96 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 111
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 96 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 111)))))))))))))))) (allB_succ' 17 95 111 (Eq.refl Bool.true) (allA_succ_of_accept 16 95 111 (accept_3_4
  16 95 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 95 111
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 95 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 95 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 95 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 111 (accept_3_4 13 95 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 95 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 95 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 111 (Polychromatic418967fa.accept_9_2_5_3_1_37 11
  95 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 111 (accept_3_4 10 95
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 111 (Polychromatic418967fa.accept_7_2_4_6_1_166
  9 95 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 111
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 111 (accept_3_4 7 95 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  111 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 95 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 95 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 111 (accept_3_4 4 95 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 95 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 95
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 111 (accept_3_4 1 95 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95 111))))))))))))))))) (allB_succ' 18 94 111 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 94 111 (accept_3_5 17 94 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  94 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 94 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 94 111 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 94 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 111 (accept_3_5 14 94 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 111
  (Polychromatic418967fa.accept_21_12_10_6_1_1191 12 94 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 94 111 (accept_3_5 11 94 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  94 111 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 94 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 94 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 111 (accept_3_5 8 94 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 94 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 111
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 94 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 111 (accept_3_5 5 94 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  111 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 94 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 94 111 (Polychromatic418967fa.accept_14_3_10_13_1_339 3 94 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 111 (accept_3_5 2 94 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 94 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 111)))))))))))))))))) (allB_succ' 19 93 111 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 93 111 3 6 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 93 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 93 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 111 (Polychromatic418967fa.accept_15_1_3_6_1_621 16 93 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 111 3 5 31 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 111 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 93 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 93 111 3 4 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 93 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 93 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 93 111 3 3 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 93 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 93 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 111 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 93 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 111 3 2 31 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 111
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 93 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 93 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 111 3 1 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 111
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 93 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 93 111))))))))))))))))))) (allB_succ' 20 92 111 (Eq.refl Bool.true) (allA_succ_of_accept 19 92 111
  (accept_3_4 19 92 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 92 111
  (Polychromatic418967fa.accept_12_6_8_3_1_82 18 92 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 92 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 111 (accept_3_4 16 92 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 92 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 92 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 111 (Polychromatic418967fa.accept_9_5_2_3_1_194 14
  92 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 92 111 (accept_3_4 13 92
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 92 111
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 92 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 92 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 111 (accept_3_4 10 92 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 92 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 92 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 111 (Polychromatic418967fa.accept_9_8_2_3_1_447 8
  92 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 92 111 (accept_3_4 7 92 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 6
  92 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 92 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 92 111 (accept_3_4 4 92 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 92
  111 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 92 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 92 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 92 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 111 (accept_3_4 1 92 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92 111)))))))))))))))))))) (allB_succ' 21 91 111 (Eq.refl Bool.true) (allA_succ_of_accept 20 91
  111 (accept_3_5 20 91 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 111
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 19 91 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 91 111 (Polychromatic418967fa.accept_15_3_1_6_1_206 18 91 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 111 (accept_3_5 17 91 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 91 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 15
  91 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 111 (accept_3_5 14 91
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 111
  (Polychromatic418967fa.accept_9_4_1_3_1_190 13 91 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 91 111 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 91 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 111 (accept_3_5 11 91 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 91 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 91 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 111 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9
  91 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 111 (accept_3_5 8 91 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 111 (Polychromatic418967fa.accept_9_7_1_3_1_443 7
  91 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 111
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 91 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 111 (accept_3_5 5 91 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  111 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 111 (Polychromatic418967fa.accept_15_3_1_6_1_206 3 91 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 111 (accept_3_5 2 91 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 111 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 91 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 111))))))))))))))))))))) (allB_succ' 22 90 111 (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 90 111 3 7 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 90 111 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 90 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 111 (Polychromatic418967fa.accept_13_6_12_7_1_5131
  19 90 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 111 3 6 30 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 111 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 90 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 111 3 5 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 111 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 90 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 90 111 3 4 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 90 111 (Polychromatic418967fa.accept_13_11_12_7_1_2443 11 90 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 111 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 90
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 90 111 3 3 30 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 90 111
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 90 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 90 111 (Polychromatic418967fa.accept_14_7_6_13_1_4111 7 90 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 111 3 2 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 111
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 90 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 90 111 3 1 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 90 111 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 90 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90 111)))))))))))))))))))))) (allB_succ' 23 89
  111 (Eq.refl Bool.true) (allA_succ_of_accept 22 89 111 (accept_3_4 22 89 111 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 89 111 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 89 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 111 (accept_3_4 19 89 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  89 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 111
  (Polychromatic418967fa.accept_13_4_11_7_1_558 17 89 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 111 (accept_3_4 16 89 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 89 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 111 (accept_3_4 13 89 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 111 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 89 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 111
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 89 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 111 (accept_3_4 10 89 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 111 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 89 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 111 (accept_3_4 7 89 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 111
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 89 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 111 (accept_3_4 4 89 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  111 (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 89 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 89 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 111 (accept_3_4 1 89 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 89 111))))))))))))))))))))))) (allB_succ' 24 88 111 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 88 111 (accept_3_5 23 88 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 111 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 88 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 111 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 88 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 111 (accept_3_5 20 88 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 111
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 88 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 111 (accept_3_5 17 88 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 88 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 111 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 88 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 111 (accept_3_5 14 88 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 111
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 88 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 111 (accept_3_5 11 88 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 88 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 88 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 111 (accept_3_5 8 88 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 111
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 88 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 111 (accept_3_5 5 88 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  111 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 88 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 88 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 88 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 111 (accept_3_5 2 88 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 88 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88 111)))))))))))))))))))))))) (allB_succ' 25 87 111 (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 87 111 3 8 29 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 87 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 87 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 22
  87 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 111 3 7 29 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 111
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 87 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 87 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 111 3 6 29 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 111 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 87 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 111
  (Polychromatic418967fa.accept_7_2_3_6_1_4 16 87 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 111 3 5 29 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 111 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 87 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 87 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 111 3 4 29 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 111
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 87 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 87 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 111 3 3 29 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 111 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 87 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 111
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 87 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 111 3 2 29 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 111 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 87 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 111 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 87 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 111 3 1 29 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 111
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 87 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 87 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87 111))))))))))))))))))))))))) (allB_succ' 26 86 111 (Eq.refl Bool.true)
  (allA_succ_of_accept 25 86 111 (accept_3_4 25 86 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 86 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 86 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 111 (accept_3_4 22 86 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 111
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 86 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 111 (accept_3_4 19 86 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 86 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 111 (accept_3_4 16 86 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 86 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 111
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 14 86 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 111 (accept_3_4 13 86 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 111 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 86 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 86 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 111 (accept_3_4 10 86 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 111
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 86 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 111 (accept_3_4 7 86 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  111 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 86 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 111 (accept_3_4 4 86 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 86 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 111 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 86
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 111 (accept_3_4 1 86 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86 111)))))))))))))))))))))))))) (allB_succ' 27 85 111 (Eq.refl
  Bool.true) (allA_succ_of_accept 26 85 111 (accept_3_5 26 85 111 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 85 111 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 85 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 111 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 85 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 111 (accept_3_5 23 85 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 22
  85 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 111
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 85 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 111 (accept_3_5 20 85 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 85 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 111 (accept_3_5 17 85 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 111
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 85 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 111 (accept_3_5 14 85 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 111 (Polychromatic418967fa.accept_32_13_21_15_1_5130 13 85 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 85 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 111 (accept_3_5 11 85 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 111
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 85 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 111 (accept_3_5 8 85 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  111 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 85 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 85 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 111 (accept_3_5 5 85 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 85 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 111 (Polychromatic418967fa.accept_15_3_10_6_1_632 3
  85 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 111 (accept_3_5 2 85 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 111 (Polychromatic418967fa.accept_9_1_4_3_1_201 1
  85 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 111)))))))))))))))))))))))))))
  (allB_succ' 28 84 111 (Eq.refl Bool.true) (allA_succ_of_gcd 27 84 111 3 9 28 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 84 111
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 26 84 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 111 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 84 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 111 3 8 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 111 (Polychromatic418967fa.accept_17_6_16_9_1_5129 23 84 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 111
  (Polychromatic418967fa.accept_13_9_6_7_1_551 22 84 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 84 111 3 7 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 84 111 (Polychromatic418967fa.accept_18_2_12_3_1_2707 20 84 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 111 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 84 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 111 3 6 28 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 111
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 84 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 111 (Polychromatic418967fa.accept_15_1_9_6_1_1323 16 84 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 84 111 3 5 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 84 111 (Polychromatic418967fa.accept_13_1_6_7_1_550 14 84 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 111
  (Polychromatic418967fa.accept_17_13_16_9_1_5128 13 84 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 111 3 4 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 111 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 84 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 111 (Polychromatic418967fa.accept_17_10_16_9_1_5127 10 84
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 111 3 3 28 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 111
  (Polychromatic418967fa.accept_16_8_4_15_1_2941 8 84 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 84 111 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 84 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 111 3 2 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 111 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 84 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 111
  (Polychromatic418967fa.accept_13_4_6_7_1_2471 4 84 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 84 111 3 1 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 84 111 (Polychromatic418967fa.accept_18_2_12_3_1_2707 2 84 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 111 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 84 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84 111)))))))))))))))))))))))))))) (allB_succ'
  29 83 111 (Eq.refl Bool.true) (allA_succ_of_accept 28 83 111 (accept_3_4 28 83 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 83 111 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 83 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 26
  83 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 111 (accept_3_4 25 83
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 111
  (Polychromatic418967fa.accept_9_6_2_3_1_771 24 83 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 83 111 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 83 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 111 (accept_3_4 22 83 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 83 111 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 83 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 20
  83 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 111 (accept_3_4 19 83
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 111
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 83 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 83 111 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 83 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 111 (accept_3_4 16 83 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 83 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 83 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 14
  83 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 111 (accept_3_4 13 83
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 111
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 83 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 83 111 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 83 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 111 (accept_3_4 10 83 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 83 111 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 83 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 111 (accept_3_4 7 83 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 6
  83 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 111
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 83 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 111 (accept_3_4 4 83 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  111 (Polychromatic418967fa.accept_21_3_20_6_1_5126 3 83 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 83 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 83 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 111 (accept_3_4 1 83 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 83 111))))))))))))))))))))))))))))) (allB_succ' 30 82 111 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 82 111 (accept_3_5 29 82 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 111 (Polychromatic418967fa.accept_11_6_5_1_1_586 28 82 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 111 (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 82 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 111 (accept_3_5 26 82 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 111
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 82 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 111 (accept_3_5 23 82 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 82 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 111 (accept_3_5 20 82 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 82 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 111
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 82 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 111 (accept_3_5 17 82 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 111 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 82 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 82 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 111 (accept_3_5 14 82 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 111
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 82 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 111 (accept_3_5 11 82 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 111 (Polychromatic418967fa.accept_13_10_4_7_1_2465 10 82 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 111 (accept_3_5 8 82 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 82 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 111
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 82 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 111 (accept_3_5 5 82 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  111 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 82 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 111 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 82 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 111 (accept_3_5 2 82 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 111)))))))))))))))))))))))))))))) (allB_succ' 31 81 111 (Eq.refl
  Bool.true) (allA_succ_of_gcd 30 81 111 3 10 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 81 111 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 81 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 111 (Polychromatic418967fa.accept_20_8_1_11_1_5125
  28 81 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 81 111 3 9 27 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 81 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 111 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 81 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 111 3 8 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 81 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 81 111 3 7 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 81 111 (Polychromatic418967fa.accept_18_2_9_3_1_3825 20 81 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 81 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 81 111 3 6 27 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 81 111
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 81 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 81 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 111 3 5 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 111
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 81 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 81 111 3 4 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 81 111 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 81 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 81 111 3 3 27 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 81 111
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 81 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 111 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 81 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 111 3 2 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 81 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 111
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 4 81 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 81 111 3 1 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 81 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 111 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 81 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 111)))))))))))))))))))))))))))))))
  (allB_succ' 32 80 111 (Eq.refl Bool.true) (allA_succ_of_accept 31 80 111 (accept_3_4 31 80 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 80 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 80 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 80 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 80 111 (accept_3_4 28 80 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  80 111 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 80 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 80 111 (Polychromatic418967fa.accept_15_11_5_6_1_669 26 80 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 80 111 (accept_3_4 25 80 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 80 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 80 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 80 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 80 111 (accept_3_4 22 80 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  80 111 (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 80 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 80 111 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 80 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 80 111 (accept_3_4 19 80 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 80 111 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 80 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 80 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 80 111 (accept_3_4 16 80 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  80 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 80 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 80 111 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 80 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 80 111 (accept_3_4 13 80 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 80 111 (Polychromatic418967fa.accept_15_12_5_6_1_2148 12 80 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 80 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 80 111 (accept_3_4 10 80 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  80 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 80 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 80 111 (Polychromatic418967fa.accept_13_8_2_7_1_2452 8 80 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 111 (accept_3_4 7 80 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 80 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 80 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 80 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 80
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 111 (accept_3_4 4 80 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 111 (Polychromatic418967fa.accept_14_3_10_13_1_339
  3 80 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 111
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 80 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 80 111 (accept_3_4 1 80 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  111)))))))))))))))))))))))))))))))) (allB_succ' 33 79 111 (Eq.refl Bool.true) (allA_succ_of_accept 32 79 111
  (accept_3_5 32 79 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 111
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 79 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 79 111 (Polychromatic418967fa.accept_18_12_7_3_1_2666 30 79 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 111 (accept_3_5 29 79 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 79 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 111 (Polychromatic418967fa.accept_18_9_7_3_1_3871
  27 79 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 111 (accept_3_5 26
  79 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 111
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 79 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 79 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 79 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 111 (accept_3_5 23 79 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 79 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 79 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 111 (Polychromatic418967fa.accept_11_10_2_1_1_1036
  21 79 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 111 (accept_3_5 20
  79 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 111
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 79 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 79 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 79 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 111 (accept_3_5 17 79 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 79 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  79 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 111 (accept_3_5 14 79
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 111 (Polychromatic418967fa.accept_9_4_7_3_1_43
  13 79 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 111
  (Polychromatic418967fa.accept_10_2_9_1_1_185 12 79 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 111 (accept_3_5 11 79 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 79 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 111 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 79 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 111 (accept_3_5 8 79 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 111 (Polychromatic418967fa.accept_21_7_16_6_1_3516 7 79 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 111
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 79 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 111 (accept_3_5 5 79 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  111 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 79 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 111 (accept_3_5 2 79 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 79 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 111))))))))))))))))))))))))))))))))) (allB_succ' 34 78 111
  (Eq.refl Bool.true) (allA_succ_of_gcd 33 78 111 3 11 26 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 78 111 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 78 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 111
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 78 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 111 3 10 26 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 78 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 78 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 78 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 111 3 9 26 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 78 111
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 78 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 78 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 111 3 8 26 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 78 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 111
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 78 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 78 111 3 7 26 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 78 111 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 78 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 78 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 111 3 6 26 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 78 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 78 111 3 5 26 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 78 111 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 78 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 111 3 4 26 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 111 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 78 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 78 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 111 3 3 26 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 111
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 78 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 78 111 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 78 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 111 3 2 26 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 111
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 78 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 78 111 3 1 26 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 78 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 78 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 111))))))))))))))))))))))))))))))))))
  (allB_succ' 35 77 111 (Eq.refl Bool.true) (allA_succ_of_accept 34 77 111 (accept_3_4 34 77 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 77 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 77 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 111
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 77 111 (accept_3_4 31 77 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  77 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 77 111 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 77 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 111 (accept_3_4 28 77 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 77 111 (Polychromatic418967fa.accept_15_12_2_6_1_2127 27 77 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 111 (accept_3_4 25 77 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 77 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 111 (Polychromatic418967fa.accept_13_10_12_7_1_1079 23 77 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 111 (accept_3_4 22 77 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 77 111 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 77 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 111
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 111 (accept_3_4 19 77 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 111 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 77 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 111 (accept_3_4 16 77 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 77 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 77 111 (accept_3_4 13 77 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  77 111 (Polychromatic418967fa.accept_15_12_2_6_1_2127 12 77 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 77 111 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 77 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 111 (accept_3_4 10 77 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 111 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 77 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 111
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 111 (accept_3_4 7 77 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77
  111 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 77 111 (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 77 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 111 (accept_3_4 4 77 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 77 111 (Polychromatic418967fa.accept_16_3_13_15_1_1913 3 77 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 111 (accept_3_4 1 77 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77 111))))))))))))))))))))))))))))))))))) (allB_succ' 36 76 111
  (Eq.refl Bool.true) (allA_succ_of_accept 35 76 111 (accept_3_5 35 76 111 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 76 111 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 76 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 111 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 76 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 111 (accept_3_5 32 76 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  76 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 111
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 76 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 111 (accept_3_5 29 76 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 111 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 76 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 111 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 76 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 111 (accept_3_5 26 76 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 111
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 76 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 111 (accept_3_5 23 76 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 111 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 76 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 111 (Polychromatic418967fa.accept_14_7_6_13_1_4111 21 76 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 111 (accept_3_5 20 76 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 111
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 76 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 111 (accept_3_5 17 76 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 111 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 76 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 111 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 76 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 111 (accept_3_5 14 76 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 111
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 76 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 111 (accept_3_5 11 76 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 111 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 76 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 111 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 76 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 111 (accept_3_5 8 76 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 111
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 76 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 111 (accept_3_5 5 76 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  111 (Polychromatic418967fa.accept_13_4_11_7_1_558 4 76 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 76 111 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 76 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 111 (accept_3_5 2 76 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76 111)))))))))))))))))))))))))))))))))))) (allB_succ'
  37 75 111 (Eq.refl Bool.true) (allA_succ_of_gcd 36 75 111 3 12 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 111 (Polychromatic418967fa.accept_16_3_11_15_1_1963 35 75
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 111
  (Polychromatic418967fa.accept_10_4_5_1_1_497 34 75 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 75 111 3 11 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 75 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 75 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 111 (Polychromatic418967fa.accept_21_10_12_6_1_5124 31 75
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 111 3 10 25 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 111
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 75 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 75 111 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 75 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 111 3 9 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 111 (Polychromatic418967fa.accept_10_6_5_1_1_482 26 75 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 111
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 75 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 75 111 3 8 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 75 111 (Polychromatic418967fa.accept_16_7_11_15_1_2929 23 75 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 75 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 111 3 7 25 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 75 111
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 75 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 111 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 75 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 111 3 6 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 111 (Polychromatic418967fa.accept_13_4_10_7_1_1701 17 75 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 111
  (Polychromatic418967fa.accept_10_6_5_1_1_482 16 75 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 75 111 3 5 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 75 111 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 75 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 111 (Polychromatic418967fa.accept_19_13_18_16_1_5123 13 75
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 111 3 4 25 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 111
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 75 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 111 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 75 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 111 3 3 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 75 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 111
  (Polychromatic418967fa.accept_16_7_11_15_1_2929 7 75 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 75 111 3 2 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 75 111 (Polychromatic418967fa.accept_17_5_7_9_1_5122 5 75 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 75 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 111 3 1 25 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 111
  (Polychromatic418967fa.accept_17_2_7_9_1_2796 2 75 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 75 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 75 111))))))))))))))))))))))))))))))))))))) (allB_succ' 38 74 111 (Eq.refl
  Bool.true) (allA_succ_of_gcd 37 74 111 37 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 36 74 111 (Polychromatic418967fa.accept_21_15_11_6_1_5121 36 74 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 74 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 74 111 (accept_3_4 34 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  74 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 74 111 (Polychromatic418967fa.accept_9_5_2_3_1_194 32 74 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 74 111 (accept_3_4 31 74 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 74 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 74 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 74 111 (accept_3_4 28 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  74 111 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 74 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 74 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 111 (accept_3_4 25 74 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 74 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 74 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 74 111 (accept_3_4 22 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  74 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 74 111 (Polychromatic418967fa.accept_15_5_14_6_1_5120 20 74 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 111 (accept_3_4 19 74 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 111 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 74 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 74 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 74 111 (accept_3_4 16 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  74 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 74 111 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 74 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 111 (accept_3_4 13 74 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 74 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 74 111 (accept_3_4 10 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  74 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 74 111 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 74 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 111 (accept_3_4 7 74 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 74 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 74 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 111 (accept_3_4 4 74 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  74 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 111
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 74 111 (accept_3_4 1 74 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  111)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 73 111 (Eq.refl Bool.true) (allA_succ_of_accept 38 73 111
  (accept_3_5 38 73 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 111
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 73 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 73 111 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 73 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 73 111 (accept_3_5 35 73 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 73 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 73 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 33
  73 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 111 (accept_3_5 32 73
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 111
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 73 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 73 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 73 111 (accept_3_5 29 73 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 73 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 111 (Polychromatic418967fa.accept_13_1_8_7_1_1088
  27 73 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 111 (accept_3_5 26
  73 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 111
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 73 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 73 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 73 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 111 (accept_3_5 23 73 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 73 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 111 (Polychromatic418967fa.accept_12_9_1_3_1_350
  21 73 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 111 (accept_3_5 20
  73 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 111
  (Polychromatic418967fa.accept_15_4_13_6_1_642 19 73 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 73 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 111 (accept_3_5 17 73 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 73 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 15
  73 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 111 (accept_3_5 14 73
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 111
  (Polychromatic418967fa.accept_9_4_1_3_1_190 13 73 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 73 111 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 73 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 111 (accept_3_5 11 73 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 73 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 73
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 111 (accept_3_5 8 73 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 111 (Polychromatic418967fa.accept_9_7_1_3_1_443 7
  73 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 111 (accept_3_5 5 73 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  111 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 111 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 73 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 111 (accept_3_5 2 73 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 111 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 73 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 111))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 72 111
  (Eq.refl Bool.true) (allA_succ_of_gcd 39 72 111 3 13 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 72 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 72 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 111
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 37 72 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 111 3 12 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 111 (Polychromatic418967fa.accept_15_5_12_6_1_639 35 72 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 111 (Polychromatic418967fa.accept_21_13_9_6_1_1190 34 72
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 72 111 3 11 24 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 72 111
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 72 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 72 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 111 3 10 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 29
  72 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 111
  (Polychromatic418967fa.accept_16_12_8_15_1_5119 28 72 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 72 111 3 9 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 72 111 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 72 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 72 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 111 3 8 24 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 111
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 72 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 72 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 111 3 7 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 111 (Polychromatic418967fa.accept_15_5_12_6_1_639 20 72 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 111
  (Polychromatic418967fa.accept_10_9_2_1_1_840 19 72 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 111 3 6 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 72 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 111 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 72 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 111 3 5 24 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 111
  (Polychromatic418967fa.accept_17_14_4_9_1_2792 14 72 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 72 111 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 72 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 111 3 4 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 72 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 111
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 72 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 72 111 3 3 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 72 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 72 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 111 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 72 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 111 3 2 24 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 111
  (Polychromatic418967fa.accept_11_5_6_1_1_988 5 72 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 72 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 111 3 1 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 111 (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 72 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 111
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 72 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 111)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 71 111 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 71 111 (accept_3_4 40 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 111 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 71 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 111 (accept_3_4 37 71 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 111 (Polychromatic418967fa.accept_19_17_14_16_1_3820 36 71 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 111
  (Polychromatic418967fa.accept_13_9_6_7_1_551 35 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 111 (accept_3_4 34 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 111 (accept_3_4 31 71 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 71 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 111
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 111 (accept_3_4 28 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 111 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 71 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 111 (accept_3_4 25 71 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 71 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 111
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 111 (accept_3_4 22 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 111 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 111 (accept_3_4 19 71 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 111 (Polychromatic418967fa.accept_15_3_11_6_1_3083 18 71 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 111
  (Polychromatic418967fa.accept_11_6_5_1_1_586 17 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 111 (accept_3_4 16 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 71 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 111 (accept_3_4 13 71 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 71 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 111
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 111 (accept_3_4 10 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 111 (accept_3_4 7 71 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 71 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 111
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 111 (accept_3_4 4 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  111 (Polychromatic418967fa.accept_15_3_11_6_1_3083 3 71 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 71 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 71 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 111 (accept_3_4 1 71 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 71 111))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 70 111 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 70 111 (accept_3_5 41 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 70 111 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 70 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 111 (Polychromatic418967fa.accept_16_7_6_15_1_495 39 70 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 111 (accept_3_5 38 70 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 70 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  70 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 111
  (Polychromatic418967fa.accept_19_17_13_16_1_5118 36 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 70 111 (accept_3_5 35 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 70 111 (Polychromatic418967fa.accept_15_4_10_6_1_2997 34 70 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 111 (accept_3_5 32 70 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  70 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 70 111
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 70 111 (accept_3_5 29 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  70 111 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 70 111 (Polychromatic418967fa.accept_15_12_10_6_1_2134 27 70 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 111 (accept_3_5 26 70 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 70 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 111
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 70 111 (accept_3_5 23 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  70 111 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 70 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 70 111 (accept_3_5 20 70 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 70 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 70 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 111
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 70 111 (accept_3_5 17 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  70 111 (Polychromatic418967fa.accept_15_1_10_6_1_631 16 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 70 111 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 70 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 70 111 (accept_3_5 14 70 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 111
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 111 (accept_3_5 11 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  70 111 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 70 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 111 (accept_3_5 8 70 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 70 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 111
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 70 111 (accept_3_5 5 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70
  111 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 70 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 70 111 (Polychromatic418967fa.accept_15_3_10_6_1_632 3 70 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 111 (accept_3_5 2 70 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 70 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70 111)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 69
  111 (Eq.refl Bool.true) (allA_succ_of_gcd 42 69 111 3 14 23 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 69 111 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 69 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 111
  (Polychromatic418967fa.accept_9_4_6_3_1_179 40 69 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 69 111 3 13 23 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 69 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 69 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 111 3 12 23 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 111
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 69 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 69 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 111 3 11 23 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 111 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  69 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 111
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 69 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 69 111 3 10 23 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 69 111 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 69 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 69 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 111 3 9 23 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 111 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 69 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 111 3 8 23 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 111 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 69 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 69 111 3 7 23 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 69 111 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 69 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 69 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 111 3 6 23 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 111
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 69 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 111 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 69 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 111 3 5 23 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 111
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 69 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 69 111 3 4 23 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 69 111 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 69 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 111 3 3 23 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 111
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 69 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 111 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 69 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 111 3 2 23 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 111 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 69 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 111
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 69 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 69 111 3 1 23 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 69 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 69 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  111))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 68 111 (Eq.refl Bool.true) (allA_succ_of_accept 43 68
  111 (accept_3_4 43 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 111
  (Polychromatic418967fa.accept_9_6_5_3_1_205 42 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 68 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 111 (accept_3_4 40 68 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 68 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 68 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 111 (Polychromatic418967fa.accept_9_2_5_3_1_37 38
  68 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 111 (accept_3_4 37 68
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 111 (Polychromatic418967fa.accept_7_1_5_6_1_59
  36 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 68 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 68 111 (accept_3_4 34 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  68 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 68 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 68 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 111 (accept_3_4 31 68 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 111 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 68 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 68 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 68 111 (accept_3_4 28 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  68 111 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 68 111 (Polychromatic418967fa.accept_9_8_5_3_1_777 26 68 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 111 (accept_3_4 25 68 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 68 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 68 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 68 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 68 111 (accept_3_4 22 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  68 111 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 68 111 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 68 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 111 (accept_3_4 19 68 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 68 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 68 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 68 111 (accept_3_4 16 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  68 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 68 111 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 68 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 111 (accept_3_4 13 68 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 68 111 (Polychromatic418967fa.accept_16_12_4_15_1_5091 12 68 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 68 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 68 111 (accept_3_4 10 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  68 111 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 68 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 68 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 111 (accept_3_4 7 68 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 68 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 68 111 (accept_3_4 4 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68
  111 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 68 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 68 111 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 68 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 111 (accept_3_4 1 68 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 111)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 67 111 (Eq.refl Bool.true)
  (allA_succ_of_accept 44 67 111 (accept_3_5 44 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  67 111 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 67 111 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 67 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 67 111 (accept_3_5 41 67 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 67 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 67 111
  (Polychromatic418967fa.accept_16_7_3_15_1_2940 39 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 67 111 (accept_3_5 38 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  67 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 67 111 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 67 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 67 111 (accept_3_5 35 67 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 67 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 67 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 67 111
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 67 111 (accept_3_5 32 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  67 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 67 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 67 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 67 111 (accept_3_5 29 67 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 67 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 111
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 67 111 (accept_3_5 26 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  67 111 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 67 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 67 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 67 111 (accept_3_5 23 67 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 67 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 67 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 111
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 67 111 (accept_3_5 20 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  67 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 67 111 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 67 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 111 (accept_3_5 17 67 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 111
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 111 (accept_3_5 14 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  67 111 (Polychromatic418967fa.accept_15_13_7_6_1_682 13 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 67 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 67 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 111 (accept_3_5 11 67 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 67 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 111
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 111 (accept_3_5 8 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67
  111 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 67 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 67 111 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 67 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 111 (accept_3_5 5 67 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 67 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  67 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 111 (accept_3_5 2 67 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 111 (Polychromatic418967fa.accept_9_1_4_3_1_201 1
  67 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  111))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 66 111 (Eq.refl Bool.true) (allA_succ_of_gcd 45 66 111
  3 15 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66
  111 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 66 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 66 111 (Polychromatic418967fa.accept_18_7_12_3_1_804 43 66 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 111 3 14 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 111
  (Polychromatic418967fa.accept_12_4_6_3_1_332 40 66 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 66 111 3 13 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 66 111 (Polychromatic418967fa.accept_12_2_6_3_1_331 38 66 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 111 3 12 22 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 111
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 66 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 111 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 66 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 66 111 3 11 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 66 111 (Polychromatic418967fa.accept_7_4_3_6_1_340 32
  66 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 111
  (Polychromatic418967fa.accept_14_3_10_13_1_339 31 66 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 111 3 10 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 111 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 66 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 111 3 9 22 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 111
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 66 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 66 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 111 3 8 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 66 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 111
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 66 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 66 111 3 7 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 66 111 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 66 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 111 (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 66 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 111 3 6 22 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 66 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 66 111 3 5 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 66 111 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 66 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 66 111 3 4 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 66 111 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 66 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 111 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 66 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 111 3 3 22 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 111
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 66 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 66 111 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 66 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 111 3 2 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 111
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 66 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 66 111 3 1 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 66 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 66 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  111)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 65 111 (Eq.refl Bool.true) (allA_succ_of_accept 46 65
  111 (accept_3_4 46 65 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 111
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 65 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 65 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 111 (accept_3_4 43 65 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 65 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 111 (Polychromatic418967fa.accept_9_5_2_3_1_194 41
  65 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 111 (accept_3_4 40 65
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 111
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 65 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 65 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 111 (accept_3_4 37 65 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 65 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 65 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 111 (Polychromatic418967fa.accept_9_8_2_3_1_447 35
  65 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 111 (accept_3_4 34 65
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 111
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 65 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 65 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 111 (accept_3_4 31 65 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 65 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 29
  65 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 111 (accept_3_4 28 65
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 111
  (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 65 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 65 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 111 (accept_3_4 25 65 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 65 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 65 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 111 (Polychromatic418967fa.accept_9_5_2_3_1_194 23
  65 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 111 (accept_3_4 22 65
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 111
  (Polychromatic418967fa.accept_12_9_5_3_1_782 21 65 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 65 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 65 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 111 (accept_3_4 19 65 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 65 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 17
  65 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 111 (accept_3_4 16 65
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 111 (Polychromatic418967fa.accept_7_1_2_6_1_55
  15 65 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 111 (accept_3_4 13 65 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 111 (Polychromatic418967fa.accept_15_12_5_6_1_2148 12 65 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 65 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 111 (accept_3_4 10 65 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 111 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 65 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 111
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 111 (accept_3_4 7 65 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  111 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 111 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 65 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 111 (accept_3_4 4 65 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 65 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 111 (accept_3_4 1 65 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65 111))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  48 64 111 (Eq.refl Bool.true) (allA_succ_of_accept 47 64 111 (accept_3_5 47 64 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 64 111 (Polychromatic418967fa.accept_19_8_7_16_1_5117 46 64 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 111
  (Polychromatic418967fa.accept_10_5_4_1_1_842 45 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 111 (accept_3_5 44 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 64 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 111 (accept_3_5 41 64 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 64 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 111
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 39 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 111 (accept_3_5 38 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 111 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 64 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 111 (accept_3_5 35 64 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 111 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 64 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 111
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 111 (accept_3_5 32 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 64 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 111 (accept_3_5 29 64 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 111 (Polychromatic418967fa.accept_15_13_4_6_1_3046 28 64 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 111
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 111 (accept_3_5 26 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 64 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 111 (accept_3_5 23 64 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 111 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 64 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 111
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 111 (accept_3_5 20 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 111 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 64 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 111 (accept_3_5 17 64 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 64 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 111
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 111 (accept_3_5 14 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 64 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 111 (accept_3_5 11 64 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 111 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 64 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 111
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 111 (accept_3_5 8 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  111 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 64 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 111 (accept_3_5 5 64 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 111 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 64 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 111 (Polychromatic418967fa.accept_21_3_1_6_1_1162 3
  64 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 111 (accept_3_5 2 64 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  111)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 63 111 (Eq.refl Bool.true) (allA_succ_of_gcd 48 63
  111 3 16 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  63 111 (Polychromatic418967fa.accept_19_9_6_16_1_5116 47 63 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 63 111 (Polychromatic418967fa.accept_15_1_3_6_1_621 46 63 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 111 3 15 21 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 111
  (Polychromatic418967fa.accept_13_5_11_7_1_559 44 63 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 111 (Polychromatic418967fa.accept_13_4_11_7_1_558 43 63 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 111 3 14 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 111 (Polychromatic418967fa.accept_15_11_3_6_1_1306
  41 63 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 111
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 40 63 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 63 111 3 13 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 63 111 (Polychromatic418967fa.accept_10_8_3_1_1_1316 38 63 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 111 (Polychromatic418967fa.accept_11_4_8_1_1_1047 37 63 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 111 3 12 21 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 111
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 35 63 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 111 (Polychromatic418967fa.accept_14_6_7_13_1_3158 34 63 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 111 3 11 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 111 (Polychromatic418967fa.accept_10_2_3_1_1_481 32
  63 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 111
  (Polychromatic418967fa.accept_13_5_11_7_1_559 31 63 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 63 111 3 10 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 63 111 (Polychromatic418967fa.accept_13_3_11_7_1_2488 29 63 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 111 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 63 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 111 3 9 21 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 111
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 63 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 111 (Polychromatic418967fa.accept_13_12_11_7_1_2491 25 63 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 111 3 8 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 111 (Polychromatic418967fa.accept_25_23_13_11_1_5115 23 63
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 111
  (Polychromatic418967fa.accept_10_2_3_1_1_481 22 63 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 63 111 3 7 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 63 111 (Polychromatic418967fa.accept_14_6_7_13_1_3158 20 63 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 111 (Polychromatic418967fa.accept_18_1_9_3_1_2672 19 63 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 111 3 6 21 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 111
  (Polychromatic418967fa.accept_13_4_11_7_1_558 17 63 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 111 (Polychromatic418967fa.accept_13_3_11_7_1_2488 16 63 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 111 3 5 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 111 (Polychromatic418967fa.accept_13_1_11_7_1_1704 14 63 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 111
  (Polychromatic418967fa.accept_18_13_9_3_1_5114 13 63 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 63 111 3 4 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 63 111 (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 63 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 111 (Polychromatic418967fa.accept_15_10_3_6_1_3042 10 63
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 111 3 3 21 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 111
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 63 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 111 (Polychromatic418967fa.accept_18_7_9_3_1_800 7 63 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 111 3 2 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 111 (Polychromatic418967fa.accept_13_5_11_7_1_559 5 63 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 111
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 63 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 63 111 3 1 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 63 111 (Polychromatic418967fa.accept_10_2_3_1_1_481 2 63 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 111 (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 63 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  111))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 62 111 (Eq.refl Bool.true) (allA_succ_of_accept 49
  62 111 (accept_3_4 49 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 111
  (Polychromatic418967fa.accept_18_12_8_3_1_1627 48 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 62 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 111 (accept_3_4 46 62 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 111 (Polychromatic418967fa.accept_21_2_20_6_1_2277
  44 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 111 (accept_3_4 43
  62 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 111
  (Polychromatic418967fa.accept_9_6_8_3_1_183 42 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 111 (accept_3_4 40 62 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 111 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 62 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 111 (Polychromatic418967fa.accept_9_2_8_3_1_181 38
  62 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 111 (accept_3_4 37 62
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 111
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 62 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 62 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 111 (accept_3_4 34 62 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 62 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 111 (Polychromatic418967fa.accept_9_5_8_3_1_437 32
  62 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 111 (accept_3_4 31 62
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 111
  (Polychromatic418967fa.accept_12_6_2_3_1_354 30 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 62 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 111 (accept_3_4 28 62 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 62 111 (Polychromatic418967fa.accept_15_12_2_6_1_2127 27 62 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 111
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 111 (accept_3_4 25 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 62 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 111 (accept_3_4 22 62 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 111
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 111 (accept_3_4 19 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 111 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 111 (accept_3_4 16 62 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 62 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 111
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 111 (accept_3_4 13 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 111 (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 62 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 111 (accept_3_4 10 62 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 111
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 8 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 111 (accept_3_4 7 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  111 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 62 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 111 (accept_3_4 4 62 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 111 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 62 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 111 (Polychromatic418967fa.accept_9_2_8_3_1_181 2
  62 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 111 (accept_3_4 1 62 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62 111))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 61 111 (Eq.refl Bool.true) (allA_succ_of_accept 50 61 111 (accept_3_5 50 61 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 111 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 61 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 111
  (Polychromatic418967fa.accept_14_6_5_13_1_367 48 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 111 (accept_3_5 47 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 111 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 61 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 111 (accept_3_5 44 61 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 61 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 111 (accept_3_5 41 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 61 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 111 (accept_3_5 38 61 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 111 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 61 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 111
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 111 (accept_3_5 35 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 111 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 61 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 111 (accept_3_5 32 61 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 111 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 61 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 111 (accept_3_5 29 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 111 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 61 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 111 (accept_3_5 26 61 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 61 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 111
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 111 (accept_3_5 23 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 111 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 61 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 111 (accept_3_5 20 61 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 111 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 61 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 111 (accept_3_5 17 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 61 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 111 (accept_3_5 14 61 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 111 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 61 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 111
  (Polychromatic418967fa.accept_16_12_13_15_1_1966 12 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 61 111 (accept_3_5 11 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 61 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 111 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 61 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 111 (accept_3_5 8 61 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 111 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7
  61 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 111 (accept_3_5 5 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  111 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 111 (Polychromatic418967fa.accept_13_3_9_7_1_1730 3 61 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 111 (accept_3_5 2 61 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 61 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 111)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 60 111 (Eq.refl Bool.true) (allA_succ_of_gcd 51 60 111 3 17 20 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 60 111
  (Polychromatic418967fa.accept_9_5_6_3_1_40 50 60 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 60 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 60 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 111 3 16 20 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 47
  60 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 111
  (Polychromatic418967fa.accept_9_1_6_3_1_177 46 60 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 60 111 3 15 20 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 60 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 60 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 111 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 60 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 111 3 14 20 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 111
  (Polychromatic418967fa.accept_9_5_6_3_1_40 41 60 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 60 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 60 111 3 13 20 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 60 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 38
  60 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 111
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 60 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 60 111 3 12 20 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 60 111 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 60 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 60 111 (Polychromatic418967fa.accept_9_7_6_3_1_456 34 60 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 60 111 3 11 20 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 60 111
  (Polychromatic418967fa.accept_9_5_6_3_1_40 32 60 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 60 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 60 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 111 3 10 20 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 111 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  60 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 111
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 60 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 60 111 3 9 20 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 60 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 60 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 111 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 60 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 111 3 8 20 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 111
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 60 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 60 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 60 111 3 7 20 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 60 111 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 60 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 111
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 60 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 111 3 6 20 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 60 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 60 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 111 3 5 20 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 111
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 60 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 60 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 60 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 111 3 4 20 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 111 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 60 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 111
  (Polychromatic418967fa.accept_7_3_4_6_1_329 10 60 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 60 111 3 3 20 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 60 111 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 60 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 111 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 60 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 111 3 2 20 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 111
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 60 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 60 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 60 111 3 1 20 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 60 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 60 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 111
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 60 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 111)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 59 111 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 59 111 (accept_3_4 52 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 59 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 111 (accept_3_4 49 59 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 111 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 59 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 111
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 111 (accept_3_4 46 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 111 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 111 (accept_3_4 43 59 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 59 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 111
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 111 (accept_3_4 40 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 111 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 59 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 111 (accept_3_4 37 59 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 111 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 59 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 111
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 111 (accept_3_4 34 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 111 (accept_3_4 31 59 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 59 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 111
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 111 (accept_3_4 28 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 111 (Polychromatic418967fa.accept_22_5_15_1_1_5113 27 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 59 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 111 (accept_3_4 25 59 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 59 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 111
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 111 (accept_3_4 22 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 111 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 111 (accept_3_4 19 59 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 111 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 59 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 111
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 111 (accept_3_4 16 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 59 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 111 (accept_3_4 13 59 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 111 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 59 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 111
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 111 (accept_3_4 10 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 111 (accept_3_4 7 59 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 59 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 111 (Polychromatic418967fa.accept_10_5_9_1_1_187 5
  59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 111 (accept_3_4 4 59 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 111 (Polychromatic418967fa.accept_16_3_11_15_1_1963
  3 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 111
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 111 (accept_3_4 1 59 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  111))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 58 111 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 58 111 (accept_3_5 53 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  58 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 58 111 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 111 (accept_3_5 50 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 58 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 111
  (Polychromatic418967fa.accept_13_9_6_7_1_551 48 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 58 111 (accept_3_5 47 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  58 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 58 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 111 (accept_3_5 44 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 58 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 58 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 111
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 58 111 (accept_3_5 41 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  58 111 (Polychromatic418967fa.accept_13_1_6_7_1_550 40 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 58 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 111 (accept_3_5 38 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 111
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 111 (accept_3_5 35 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 111 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 111 (accept_3_5 32 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 58 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 111
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 111 (accept_3_5 29 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 111 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 111 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 111 (accept_3_5 26 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 111
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 111 (accept_3_5 23 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 111 (accept_3_5 20 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 58 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 111
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 111 (accept_3_5 17 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 111 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 111 (accept_3_5 14 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 111
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 111 (accept_3_5 11 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 111 (accept_3_5 8 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 58 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 111
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 111 (accept_3_5 5 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  111 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 58 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 58 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 58 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 111 (accept_3_5 2 58 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 58 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 111))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 55 57 111 (Eq.refl Bool.true) (allA_succ_of_gcd 54 57 111 3 18 19 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 111
  (Polychromatic418967fa.accept_12_5_9_3_1_85 53 57 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 57 111 (Polychromatic418967fa.accept_15_7_12_6_1_1327 52 57 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 57 111 3 17 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 57 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  57 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 111
  (Polychromatic418967fa.accept_12_1_9_3_1_370 49 57 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 57 111 3 16 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 57 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 57 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 111 3 15 19 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 111
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 57 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 111 (Polychromatic418967fa.accept_11_10_2_1_1_1036 43 57 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 57 111 3 14 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 57 111 (Polychromatic418967fa.accept_12_5_9_3_1_85 41
  57 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 111
  (Polychromatic418967fa.accept_7_5_1_6_1_163 40 57 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 57 111 3 13 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 57 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 57 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 111 3 12 19 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 111
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 57 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 57 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 57 111 3 11 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 57 111 (Polychromatic418967fa.accept_11_10_2_1_1_1036
  32 57 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 111
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 57 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 57 111 3 10 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 57 111 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 57 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 111 (Polychromatic418967fa.accept_13_2_5_7_1_1695 28 57 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 111 3 9 19 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 111 (Polychromatic418967fa.accept_11_3_2_1_1_994 25 57 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 57 111 3 8 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 57 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 57 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 57 111 3 7 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 57 111 (Polychromatic418967fa.accept_15_5_12_6_1_639 20 57 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 57 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 111 3 6 19 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 111
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 57 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 57 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 57 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 57 111 3 5 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 57 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 111
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 57 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 57 111 3 4 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 57 111 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 57 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 111 3 3 19 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 111
  (Polychromatic418967fa.accept_16_8_9_15_1_5112 8 57 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 111 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 57 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 111 3 2 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 57 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 111
  (Polychromatic418967fa.accept_10_4_7_1_1_471 4 57 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 57 111 3 1 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 57 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 111 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 57 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  111))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 111 (allA_succ_of_accept 55 56 111
  (accept_3_4 55 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 56 111
  (Polychromatic418967fa.accept_12_6_8_3_1_82 54 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 56 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 111 (accept_3_4 52 56 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 56 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 56 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 111 (Polychromatic418967fa.accept_9_5_2_3_1_194 50
  56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 56 111 (accept_3_4 49 56
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 56 111
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 48 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 56 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 111 (accept_3_4 46 56 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 56 111 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 56 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 111 (Polychromatic418967fa.accept_9_8_2_3_1_447 44
  56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 56 111 (accept_3_4 43 56
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 56 111
  (Polychromatic418967fa.accept_9_6_2_3_1_771 42 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 56 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 111 (accept_3_4 40 56 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 56 111 (Polychromatic418967fa.accept_15_9_11_6_1_637 39 56 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 111 (Polychromatic418967fa.accept_13_12_4_7_1_2520
  38 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 56 111 (accept_3_4 37
  56 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 56 111
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 56 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 111 (accept_3_4 34 56 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 56 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 56 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 111 (Polychromatic418967fa.accept_9_5_2_3_1_194 32
  56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 56 111 (accept_3_4 31 56
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 56 111
  (Polychromatic418967fa.accept_12_6_8_3_1_82 30 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 56 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 111 (accept_3_4 28 56 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 56 111 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 56 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 111 (Polychromatic418967fa.accept_9_8_2_3_1_447 26
  56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 56 111 (accept_3_4 25 56
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 56 111
  (Polychromatic418967fa.accept_9_6_2_3_1_771 24 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 56 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 111 (accept_3_4 22 56 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 56 111 (Polychromatic418967fa.accept_19_2_18_16_1_5111 21 56 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 111
  (Polychromatic418967fa.accept_15_5_11_6_1_692 20 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 111 (accept_3_4 19 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 111 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 111 (accept_3_4 16 56 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 56 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 111
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 111 (accept_3_4 13 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 111 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 111 (accept_3_4 10 56 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 111 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 56 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 111
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 111 (accept_3_4 7 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  111 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 111 (accept_3_4 4 56 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 111 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 56 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 111 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2
  56 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 111 (accept_3_4 1 56 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 111))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 111 (allA_succ_of_accept 54 55 111 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 55 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 111 (accept_3_5 53 55 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 55 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 111
  (Polychromatic418967fa.accept_9_6_1_3_1_191 51 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 55 111 (accept_3_5 50 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  55 111 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 55 111 (Polychromatic418967fa.accept_13_9_3_7_1_1065 48 55 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 111 (accept_3_5 47 55 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 55 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 111
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 111 (accept_3_5 44 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 111 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 55 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 111 (accept_3_5 41 55 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 55 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 111
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 111 (accept_3_5 38 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 111 (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 111 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 55 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 111 (accept_3_5 35 55 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 55 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 111
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 111 (accept_3_5 32 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 111 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 111 (Polychromatic418967fa.accept_13_4_3_7_1_2515 30 55 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 111 (accept_3_5 29 55 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 111
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 111 (accept_3_5 26 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 111 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 55 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 111 (accept_3_5 23 55 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 55 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 111
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 111 (accept_3_5 20 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 111 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 111 (Polychromatic418967fa.accept_15_3_10_6_1_632 18 55 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 111 (accept_3_5 17 55 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 111
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 111 (accept_3_5 14 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 111 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 111 (Polychromatic418967fa.accept_15_12_10_6_1_2134 12 55 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 111 (accept_3_5 11 55 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 55 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 111
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 111 (accept_3_5 8 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  111 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 55 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 111 (accept_3_5 5 55 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 111 (Polychromatic418967fa.accept_15_3_10_6_1_632 3
  55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 111 (accept_3_5 2 55 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 111 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1
  55 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  111))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 111 (allA_succ_of_accept 53 54 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 111 (Polychromatic418967fa.accept_12_4_6_3_1_332 52 54 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 54 111 3 17 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 54 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 50
  54 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 54 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 54 111 3 16 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 54 111 (Polychromatic418967fa.accept_10_7_4_1_1_1319 47 54 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 54 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 54 111 3 15 18 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 111
  (Polychromatic418967fa.accept_12_8_6_3_1_366 44 54 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 54 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 54 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 111 3 14 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 111
  (Polychromatic418967fa.accept_12_4_6_3_1_332 40 54 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 54 111 3 13 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 54 111 (Polychromatic418967fa.accept_12_2_6_3_1_331 38 54 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 111 3 12 18 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 111
  (Polychromatic418967fa.accept_10_5_4_1_1_842 35 54 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 111 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 54 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 54 111 3 11 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 54 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 32
  54 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 111
  (Polychromatic418967fa.accept_11_9_10_1_1_581 31 54 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 111 3 10 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 111 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 54 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 111 3 9 18 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 111
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 54 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 111 3 8 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 111 (Polychromatic418967fa.accept_16_7_6_15_1_495 23 54 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 111
  (Polychromatic418967fa.accept_7_1_5_6_1_59 22 54 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 54 111 3 7 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 54 111 (Polychromatic418967fa.accept_11_9_10_1_1_581 20 54 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 111 (Polychromatic418967fa.accept_15_4_9_6_1_627 19 54 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 111 3 6 18 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 111 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 54 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 54 111 3 5 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 54 111 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 54 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 111 3 4 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 54 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 111 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 54 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 111 3 3 18 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 111
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 54 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 111 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 54 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 111 3 2 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 111
  (Polychromatic418967fa.accept_7_4_5_6_1_344 4 54 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 54 111 3 1 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 54 111 (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 54 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  111)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 111 (allA_succ_of_accept 52 53 111 (accept_3_4
  52 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 111
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 111 (accept_3_4 49 53 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 111 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 53 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 47
  53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 111 (accept_3_4 46 53
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 111
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 111 (accept_3_4 43 53 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 111 (Polychromatic418967fa.accept_9_5_8_3_1_437 41
  53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 111 (accept_3_4 40 53
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 111
  (Polychromatic418967fa.accept_19_1_15_16_1_2553 39 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 53 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 111 (accept_3_4 37 53 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 53 111 (Polychromatic418967fa.accept_16_4_5_15_1_5083 36 53 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 111
  (Polychromatic418967fa.accept_20_15_13_11_1_5110 35 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 53 111 (accept_3_4 34 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 53 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 53 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 111 (accept_3_4 31 53 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 111
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 111 (accept_3_4 28 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 111 (Polychromatic418967fa.accept_19_8_15_16_1_5109 27 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 111 (accept_3_4 25 53 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 53 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 111
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 111 (accept_3_4 22 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 111 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 111 (accept_3_4 19 53 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 111
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 111 (accept_3_4 16 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 111 (accept_3_4 13 53 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 53 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 111
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 111 (accept_3_4 10 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 111 (accept_3_4 7 53 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 111
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 111 (accept_3_4 4 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  111 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 53 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 111 (accept_3_4 1 53 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 111))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 111
  (allA_succ_of_accept 51 52 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 52 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 111 (accept_3_5 50 52 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 111 (Polychromatic418967fa.accept_11_4_8_1_1_1047
  48 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 111 (accept_3_5 47
  52 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 111
  (Polychromatic418967fa.accept_7_4_3_6_1_340 46 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 52 111 (Polychromatic418967fa.accept_14_3_10_13_1_339 45 52 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 111 (accept_3_5 44 52 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 52 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 111 (Polychromatic418967fa.accept_9_6_7_3_1_436 42
  52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 111 (accept_3_5 41 52
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 111 (Polychromatic418967fa.accept_9_4_7_3_1_43
  40 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 52 111
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 52 111 (accept_3_5 38 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  52 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 52 111 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 52 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 111 (accept_3_5 35 52 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 111 (Polychromatic418967fa.accept_22_12_8_1_1_5108 34 52 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 111
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 52 111 (accept_3_5 32 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  52 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 52 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 52 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 111 (accept_3_5 29 52 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 111 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 52 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 111
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 52 111 (accept_3_5 26 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  52 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 52 111 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 52 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 111 (accept_3_5 23 52 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 111 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 52 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 111
  (Polychromatic418967fa.accept_16_5_4_15_1_1102 21 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 52 111 (accept_3_5 20 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  52 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 52 111 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 52 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 111 (accept_3_5 17 52 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 52 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 111
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 111 (accept_3_5 14 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  52 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 52 111 (Polychromatic418967fa.accept_15_12_7_6_1_4013 12 52 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 111 (accept_3_5 11 52 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 111 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 52 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 111
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 52 111 (accept_3_5 8 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52
  111 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 52 111 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 52 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 111 (accept_3_5 5 52 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 52 111 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 52 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 111 (Polychromatic418967fa.accept_8_3_4_7_1_475 3
  52 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 111 (accept_3_5 2 52 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  111)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 111 (allA_succ_of_accept 50 51 111
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 51 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 51 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 111 3 16 17 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 111 (Polychromatic418967fa.accept_9_2_6_3_1_178 47
  51 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 111
  (Polychromatic418967fa.accept_7_4_2_6_1_337 46 51 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 111 3 15 17 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 111 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 51 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 51 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 111 3 14 17 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 111
  (Polychromatic418967fa.accept_9_5_6_3_1_40 41 51 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 51 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 111 3 13 17 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 38
  51 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 111
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 51 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 111 3 12 17 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 111 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 51 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 111 (Polychromatic418967fa.accept_9_7_6_3_1_456 34 51 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 111 3 11 17 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 111
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 51 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 51 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 111 3 10 17 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 29
  51 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 111
  (Polychromatic418967fa.accept_8_4_3_7_1_491 28 51 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 111 3 9 17 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 111 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 51 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 51 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 111 3 8 17 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 111
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 51 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 51 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 111 3 7 17 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 111 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 51 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 111
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 51 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 111 3 6 17 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 51 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 111 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 51 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 111 3 5 17 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 111
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 51 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 51 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 111 3 4 17 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 51 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 111
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 51 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 111 3 3 17 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 51 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 111 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 51 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 111 3 2 17 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 111
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 51 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 51 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 111 3 1 17 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 111 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 51 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 111
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 51 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 111))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 111 (allA_succ_of_accept 49 50 111
  (accept_3_4 49 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 111
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 48 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 111 (accept_3_4 46 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 50 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 44
  50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 111 (accept_3_4 43 50
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 111
  (Polychromatic418967fa.accept_9_6_5_3_1_205 42 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 111 (accept_3_4 40 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 50 111 (Polychromatic418967fa.accept_20_19_10_11_1_5107 39 50 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 111
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 111 (accept_3_4 37 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 111 (Polychromatic418967fa.accept_21_15_8_6_1_5106 36 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 50 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 111 (accept_3_4 34 50 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 111
  (Polychromatic418967fa.accept_19_13_12_16_1_5087 32 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 50 111 (accept_3_4 31 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 50 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 50 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 111 (accept_3_4 28 50 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 111 (Polychromatic418967fa.accept_11_5_6_1_1_988
  27 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 111
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 111 (accept_3_4 25 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 50 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 111 (accept_3_4 22 50 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 111
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 111 (accept_3_4 19 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 111 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 111 (accept_3_4 16 50 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 50 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 111
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 14 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 111 (accept_3_4 13 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 50 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 111 (accept_3_4 10 50 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 111
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 111 (accept_3_4 7 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  111 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 111 (accept_3_4 4 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 111 (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 50 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 111 (accept_3_4 1 50 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 111)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 111 (allA_succ_of_accept 48 49 111 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 49 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 111 (accept_3_5 47 49 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 111
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 111 (accept_3_5 44 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 111 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 111 (accept_3_5 41 49 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 111
  (Polychromatic418967fa.accept_11_6_5_1_1_586 39 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 111 (accept_3_5 38 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 111 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 111 (Polychromatic418967fa.accept_14_8_7_13_1_4113 36 49 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 111 (accept_3_5 35 49 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 111
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 111 (accept_3_5 32 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 111 (Polychromatic418967fa.accept_22_9_5_1_1_2204 31 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 111 (accept_3_5 29 49 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 111
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 27 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 111 (accept_3_5 26 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 111 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 111 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 49 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 111 (accept_3_5 23 49 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 111
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 111 (accept_3_5 20 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 111 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 111 (accept_3_5 17 49 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 111
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 111 (accept_3_5 14 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 111 (Polychromatic418967fa.accept_15_13_4_6_1_3046 13 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 111 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 49 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 111 (accept_3_5 11 49 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 111
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 111 (accept_3_5 8 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  111 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 111 (accept_3_5 5 49 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 111 (Polychromatic418967fa.accept_13_3_10_7_1_1061
  3 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 111 (accept_3_5 2 49
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 111 (Polychromatic418967fa.accept_9_1_4_3_1_201
  1 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  111))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 111 (allA_succ_of_accept 47 48 111
  (Polychromatic418967fa.accept_13_8_9_7_1_530 47 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 111 (Polychromatic418967fa.accept_15_1_3_6_1_621 46 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 111 3 15 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 111 (Polychromatic418967fa.accept_18_8_12_3_1_2708
  44 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 111
  (Polychromatic418967fa.accept_10_3_8_1_1_182 43 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 111 3 14 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 48 111 (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 111 (Polychromatic418967fa.accept_14_12_6_13_1_3173 40 48
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 48 111 3 13 16 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 48 111
  (Polychromatic418967fa.accept_17_4_14_9_1_5105 38 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 48 111 (Polychromatic418967fa.accept_13_11_9_7_1_2484 37 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 111 3 12 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 111 (Polychromatic418967fa.accept_14_7_6_13_1_4111
  35 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 111
  (Polychromatic418967fa.accept_13_8_9_7_1_530 34 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 48 111 3 11 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 48 111 (Polychromatic418967fa.accept_13_6_9_7_1_2430 32 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 111 (Polychromatic418967fa.accept_15_1_3_6_1_621 31 48 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 111 3 10 16 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 111
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 111 (Polychromatic418967fa.accept_13_2_9_7_1_164 28 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 48 111 3 9 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 111 (Polychromatic418967fa.accept_14_12_6_13_1_3173 26 48
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 111
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 25 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 111 3 8 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 111 (Polychromatic418967fa.accept_10_3_8_1_1_182 23 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 111 (Polychromatic418967fa.accept_17_5_14_9_1_5104 22 48
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 48 111 3 7 16 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 48 111
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 20 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 48 111 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 111 3 6 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 111 (Polychromatic418967fa.accept_13_4_9_7_1_2402 17 48 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 111
  (Polychromatic418967fa.accept_13_3_9_7_1_1730 16 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 48 111 3 5 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 48 111 (Polychromatic418967fa.accept_18_14_12_3_1_5103 14 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 111 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 48 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 111 3 4 16 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 111
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 111 (Polychromatic418967fa.accept_15_10_3_6_1_3042 10 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 111 3 3 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 111 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 48 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 111
  (Polychromatic418967fa.accept_14_7_6_13_1_4111 7 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 111 3 2 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 111 (Polychromatic418967fa.accept_14_5_6_13_1_3145 5 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 111 (Polychromatic418967fa.accept_13_4_9_7_1_2402 4 48 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 48 111 3 1 16 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 48 111
  (Polychromatic418967fa.accept_13_2_9_7_1_164 2 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 48 111 (Polychromatic418967fa.accept_15_1_3_6_1_621 1 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 48 111)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 111
  (allA_succ_of_accept 46 47 111 (accept_3_4 46 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  47 111 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 111 (accept_3_4 43 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 47 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 111
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 111 (accept_3_4 40 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 111 (accept_3_4 37 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 47 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 111
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 111 (accept_3_4 34 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 111 (accept_3_4 31 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 111 (Polychromatic418967fa.accept_20_10_7_11_1_5102 30 47 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 111
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 111 (accept_3_4 28 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 111 (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 111 (accept_3_4 25 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 47 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 111
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 111 (accept_3_4 22 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 111 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 111 (accept_3_4 19 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 47 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 111
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 111 (accept_3_4 16 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 111 (accept_3_4 13 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 111 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 47 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 111
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 111 (accept_3_4 10 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 111 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 111 (accept_3_4 7 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 47 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 111
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 111 (accept_3_4 4 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  111 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 47 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 111 (accept_3_4 1 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 47 111))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 111
  (allA_succ_of_accept 45 46 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 46 111 (accept_3_5 44 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 46 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 46 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 42
  46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 111 (accept_3_5 41 46
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 111
  (Polychromatic418967fa.accept_7_5_4_6_1_167 40 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 46 111 (Polychromatic418967fa.accept_15_9_1_6_1_657 39 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 46 111 (accept_3_5 38 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 46 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 46 111 (Polychromatic418967fa.accept_11_3_2_1_1_994
  36 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 111 (accept_3_5 35
  46 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 111
  (Polychromatic418967fa.accept_9_7_1_3_1_443 34 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 46 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 46 111 (accept_3_5 32 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 46 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 46 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 46 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 30
  46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 111 (accept_3_5 29 46
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 111
  (Polychromatic418967fa.accept_19_9_8_16_1_5101 28 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 46 111 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 111 (accept_3_5 26 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 46 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 24
  46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 111 (accept_3_5 23 46
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 111
  (Polychromatic418967fa.accept_9_4_1_3_1_190 22 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 46 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 46 111 (accept_3_5 20 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 46 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 46 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 46 111 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  18 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 111 (accept_3_5 17
  46 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 111
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 46 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 111 (accept_3_5 14 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 46 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 12
  46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 111 (accept_3_5 11 46
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 111
  (Polychromatic418967fa.accept_7_3_4_6_1_329 10 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 46 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 111 (accept_3_5 8 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 46 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 46 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 6
  46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 111 (accept_3_5 5 46 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46 111 (Polychromatic418967fa.accept_9_4_1_3_1_190 4
  46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 111
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 46 111 (accept_3_5 2 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46
  111 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 46 111)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 111 (allA_succ_of_accept 44 45 111
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 111 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 111 3 14 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 111 (Polychromatic418967fa.accept_12_5_9_3_1_85 41
  45 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 111
  (Polychromatic418967fa.accept_13_1_6_7_1_550 40 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 111 3 13 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 45 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 111 3 12 15 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 111
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 111 3 11 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 111 (Polychromatic418967fa.accept_7_4_3_6_1_340 32
  45 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 111
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 111 3 10 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 111 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 111 (Polychromatic418967fa.accept_16_12_13_15_1_1966 28 45
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 111 3 9 15 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 111 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 111 3 8 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 45 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 111 3 7 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 111 (Polychromatic418967fa.accept_17_3_11_9_1_5100 20 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 111 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 45 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 111 3 6 15 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 111
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 111 3 5 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 111
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 111 3 4 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 111 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 111 3 3 15 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 111
  (Polychromatic418967fa.accept_17_8_11_9_1_5099 8 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 111 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 111 3 2 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 111 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 45 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 111
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 111 3 1 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 111 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 45 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  111))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 111 (allA_succ_of_accept 43 44 111 (accept_3_4 43 44
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 111
  (Polychromatic418967fa.accept_9_6_8_3_1_183 42 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 111 (accept_3_4 40 44 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 44 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 38
  44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 111 (accept_3_4 37 44
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 111 (Polychromatic418967fa.accept_7_1_2_6_1_55
  36 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 44 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 44 111 (accept_3_4 34 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  44 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 44 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 44 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 111 (accept_3_4 31 44 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 111 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 44 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 44 111 (accept_3_4 28 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  44 111 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 44 111 (Polychromatic418967fa.accept_19_7_6_16_1_3818 26 44 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 111 (accept_3_4 25 44 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 44 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 44 111 (accept_3_4 22 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  44 111 (Polychromatic418967fa.accept_20_1_4_11_1_5098 21 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 44 111 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 44 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 111 (accept_3_4 19 44 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 44 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 44 111 (accept_3_4 16 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  44 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 44 111 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 44 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 111 (accept_3_4 13 44 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 111 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 44 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 44 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 44 111 (accept_3_4 10 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  44 111 (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 44 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 44 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 111 (accept_3_4 7 44 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 44 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 111 (accept_3_4 4 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  111 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 111 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 44 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 111 (accept_3_4 1 44 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 111)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 111 (allA_succ_of_accept 42 43
  111 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 111 (accept_3_5 41 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 111 (Polychromatic418967fa.accept_16_7_11_15_1_2929 39 43 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 111 (accept_3_5 38 43 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 43 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 111
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 111 (accept_3_5 35 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 43 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 111 (accept_3_5 32 43 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 111 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 43 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 111
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 111 (accept_3_5 29 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 111 (Polychromatic418967fa.accept_18_9_7_3_1_3871 27 43 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 111 (accept_3_5 26 43 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 111 (Polychromatic418967fa.accept_13_12_4_7_1_2520 25 43 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 111
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 111 (accept_3_5 23 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 111 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 43 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 111 (accept_3_5 20 43 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 43 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 111
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 111 (accept_3_5 17 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 111 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 43 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 111 (accept_3_5 14 43 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 111 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 43 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 111
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 111 (accept_3_5 11 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 43 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 111 (accept_3_5 8 43 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 111 (Polychromatic418967fa.accept_14_7_1_13_1_357 7 43 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 111
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 111 (accept_3_5 5 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  111 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 111 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 43 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 111 (accept_3_5 2 43 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 111 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 43 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 111))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 111
  (allA_succ_of_accept 41 42 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 42 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 111 3 13 14 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 111
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 42 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 111 3 12 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 111 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  42 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 111
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 42 111 3 11 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 42 111 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 42 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 111 3 10 14 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 42 111 3 9 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 42 111 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 42 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 111 3 8 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 111 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 42 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 111 3 7 14 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 111
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 42 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 111 3 6 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 111
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 42 111 3 5 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 42 111 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 111 3 4 14 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 111
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 42 111 3 3 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 42 111 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 42 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 111
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 111 3 2 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 42 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 111 3 1 14 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 111
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 42 111)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 111
  (allA_succ_of_accept 40 41 111 (accept_3_4 40 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  41 111 (Polychromatic418967fa.accept_15_9_11_6_1_637 39 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 111 (accept_3_4 37 41 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 111 (Polychromatic418967fa.accept_17_2_7_9_1_2796 36 41 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 111
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 111 (accept_3_4 34 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 111 (accept_3_4 31 41 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 111
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 111 (accept_3_4 28 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 111 (Polychromatic418967fa.accept_20_7_1_11_1_3766 27 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 111 (accept_3_4 25 41 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 41 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 111
  (Polychromatic418967fa.accept_19_4_3_16_1_5097 23 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 111 (accept_3_4 22 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 111 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 111 (accept_3_4 19 41 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 111
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 111 (accept_3_4 16 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 111 (accept_3_4 13 41 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 111 (Polychromatic418967fa.accept_20_12_1_11_1_5096 12 41 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 111
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 111 (accept_3_4 10 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 111 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 111 (accept_3_4 7 41 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 111
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 111 (accept_3_4 4 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  111 (Polychromatic418967fa.accept_15_3_11_6_1_3083 3 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 41 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 111 (accept_3_4 1 41 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 41 111))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 111 (allA_succ_of_accept
  39 40 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 40 111 (accept_3_5 38 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 40 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 40 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 40 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 111 (accept_3_5 35 40 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 111 (Polychromatic418967fa.accept_9_7_4_3_1_204 34
  40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 111
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 111 (accept_3_5 32 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 111 (Polychromatic418967fa.accept_12_6_4_3_1_361 30 40 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 111 (accept_3_5 29 40 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 111 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 40 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 111
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 27 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 111 (accept_3_5 26 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 111 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 40 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 111 (accept_3_5 23 40 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 40 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 111
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 111 (accept_3_5 20 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 40 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 111 (accept_3_5 17 40 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 111 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 40 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 111
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 111 (accept_3_5 14 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 111 (Polychromatic418967fa.accept_15_12_10_6_1_2134 12 40 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 111 (accept_3_5 11 40 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 111 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 40 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 111
  (Polychromatic418967fa.accept_16_9_8_15_1_5095 9 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 111 (accept_3_5 8 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  111 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 111 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 40 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 111 (accept_3_5 5 40 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 40 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 111 (Polychromatic418967fa.accept_13_3_1_7_1_1706 3
  40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 111 (accept_3_5 2 40 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  111)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 111 (allA_succ_of_accept 38 39 111
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 111 3 12 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 111 (Polychromatic418967fa.accept_10_5_9_1_1_187 35
  39 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 111
  (Polychromatic418967fa.accept_15_4_9_6_1_627 34 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 111 3 11 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 111 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 39 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 111 3 10 13 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 111
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 111 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 111 3 9 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 39 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 111
  (Polychromatic418967fa.accept_10_5_9_1_1_187 25 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 111 3 8 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 111 (Polychromatic418967fa.accept_10_2_9_1_1_185 22 39 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 111 3 7 13 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 111
  (Polychromatic418967fa.accept_21_20_18_6_1_5094 20 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 111 3 6 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 39 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 111
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 111 3 5 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 111 (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 111 (Polychromatic418967fa.accept_17_13_5_9_1_1762 13 39
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 111 3 4 13 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 111
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 111 3 3 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 111 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 39 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 111
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 111 3 2 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 111 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 39 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 111 3 1 13 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 111
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 111 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 111))))))))))))))))))))))))))))))))))))))) (allB_succ 38 111
  (allA_succ_of_accept 37 38 111 (accept_3_4 37 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 111 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 38 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 111 (accept_3_4 34 38 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 111
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 111 (accept_3_4 31 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 111 (accept_3_4 28 38 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 111 (Polychromatic418967fa.accept_18_9_2_3_1_5082 27 38 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 111
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 111 (accept_3_4 25 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 38 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 111 (accept_3_4 22 38 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 111
  (Polychromatic418967fa.accept_23_20_15_19_1_5092 20 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 38 111 (accept_3_4 19 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 38 111 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 38 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 38 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 111 (accept_3_4 16 38 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 15
  38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 111
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 111 (accept_3_4 13 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 111 (Polychromatic418967fa.accept_17_12_4_9_1_3889 12 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 38 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 111 (accept_3_4 10 38 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 111
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 111 (accept_3_4 7 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  111 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 111 (accept_3_4 4 38 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 111 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 38 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 38
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 111 (accept_3_4 1 38 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 111)))))))))))))))))))))))))))))))))))))) (allB_succ 37 111
  (allA_succ_of_accept 36 37 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 37 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 111 (accept_3_5 35 37 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 33
  37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 111 (accept_3_5 32 37
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 111 (Polychromatic418967fa.accept_7_3_2_6_1_56
  31 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 111 (accept_3_5 29 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 111 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 37 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 111 (accept_3_5 26 37 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 37 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 111
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 111 (accept_3_5 23 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 111 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 37 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 111 (accept_3_5 20 37 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 111 (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 37 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 111 (accept_3_5 17 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 37 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 111 (accept_3_5 14 37 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 111 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 37 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 111
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 111 (accept_3_5 11 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 111 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 37 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 111 (accept_3_5 8 37 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 111 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 37 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 111 (accept_3_5 5 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  111 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 37 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 111 (accept_3_5 2 37 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 37 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 111))))))))))))))))))))))))))))))))))))) (allB_succ 36 111
  (allA_succ_of_accept 35 36 111 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 36 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 111 (Polychromatic418967fa.accept_13_8_10_7_1_1702 34 36
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 111 3 11 12 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 111
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 111 (Polychromatic418967fa.accept_21_10_15_6_1_5090 31 36 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 111 3 10 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 111 (Polychromatic418967fa.accept_13_3_10_7_1_1061
  29 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 111
  (Polychromatic418967fa.accept_16_12_4_15_1_5091 28 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 36 111 3 9 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 36 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 36 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 111 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 36 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 111 3 8 12 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 111
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 111 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 36 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 36 111 3 7 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 36 111 (Polychromatic418967fa.accept_19_1_17_16_1_2578 20 36
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 111
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 111 3 6 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 111 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 36 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 36 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 111 3 5 12 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 111
  (Polychromatic418967fa.accept_16_14_4_15_1_3944 14 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 111 (Polychromatic418967fa.accept_11_2_3_1_1_244 13 36 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 111 3 4 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 111 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 36 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 111
  (Polychromatic418967fa.accept_21_10_15_6_1_5090 10 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 36 111 3 3 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 36 111 (Polychromatic418967fa.accept_13_8_10_7_1_1702 8 36 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 111 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 36 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 111 3 2 12 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 111
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 111 (Polychromatic418967fa.accept_13_4_10_7_1_1701 4 36 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 36 111 3 1 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 36 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 36 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 111
  (Polychromatic418967fa.accept_19_1_17_16_1_2578 1 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 111)))))))))))))))))))))))))))))))))))) (allB_succ 35 111 (allA_succ_of_accept 34 35 111 (accept_3_4 34
  35 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 111
  (Polychromatic418967fa.accept_9_6_8_3_1_183 33 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 111 (accept_3_4 31 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 111 (Polychromatic418967fa.accept_13_4_9_7_1_2402 30 35 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 111 (Polychromatic418967fa.accept_9_2_8_3_1_181 29
  35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 111 (accept_3_4 28 35
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 111
  (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 111 (accept_3_4 25 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 35 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 111 (Polychromatic418967fa.accept_9_5_8_3_1_437 23
  35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 111 (accept_3_4 22 35
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 111
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 35 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 111 (accept_3_4 19 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 35 111 (Polychromatic418967fa.accept_15_3_5_6_1_4005 18 35 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 111 (Polychromatic418967fa.accept_13_4_9_7_1_2402
  17 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 111 (accept_3_4 16
  35 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 111
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 35 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 111 (accept_3_4 13 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 35 111 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 35 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 111 (Polychromatic418967fa.accept_9_2_8_3_1_181 11
  35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 111 (accept_3_4 10 35
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 111
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 111 (accept_3_4 7 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 35 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 111 (Polychromatic418967fa.accept_9_5_8_3_1_437 5
  35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 111 (accept_3_4 4 35 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 111 (Polychromatic418967fa.accept_11_3_2_1_1_994 3
  35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 111
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 111 (accept_3_4 1 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  111))))))))))))))))))))))))))))))))))) (allB_succ 34 111 (allA_succ_of_accept 33 34 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 111 (accept_3_5 32 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 111 (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 34 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 111 (accept_3_5 29 34 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 111 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 34 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 111
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 111 (accept_3_5 26 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 111 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 34 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 111 (accept_3_5 23 34 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 111 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 34 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 111 (accept_3_5 20 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 111 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 34 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 111 (accept_3_5 17 34 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 111 (Polychromatic418967fa.accept_13_3_8_7_1_4135 16 34 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 111
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 111 (accept_3_5 14 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 111 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 34 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 111 (accept_3_5 11 34 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 111 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 34 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 111 (accept_3_5 8 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  111 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 111 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 34 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 111 (accept_3_5 5 34 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 111 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 34 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 111 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3
  34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 111 (accept_3_5 2 34 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 111))))))))))))))))))))))))))))))))))
  (allB_succ 33 111 (allA_succ_of_accept 32 33 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 33 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 111
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 111 3 10 11 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 33 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 33 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 111 3 9 11 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 33 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 111 3 8 11 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 111 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 33 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 111 3 7 11 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 111 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 33 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 33 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 111 3 6 11 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 111
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 111 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 33 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 111 3 5 11 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 111
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 111 3 4 11 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 33 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 111 3 3 11 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 111
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 111 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 33 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 111 3 2 11 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 111 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 33 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 111
  (Polychromatic418967fa.accept_7_4_5_6_1_344 4 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 111 3 1 11 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 33 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 111)))))))))))))))))))))))))))))))))
  (allB_succ 32 111 (allA_succ_of_accept 31 32 111 (accept_3_4 31 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 32 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 111 (accept_3_4 28 32 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 111 (Polychromatic418967fa.accept_13_1_6_7_1_550
  27 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 111
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 111 (accept_3_4 25 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 111 (accept_3_4 22 32 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 111 (Polychromatic418967fa.accept_19_2_13_16_1_5089 21 32 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 111
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 111 (accept_3_4 19 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 111 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 111 (accept_3_4 16 32 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 32 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 111
  (Polychromatic418967fa.accept_13_1_6_7_1_550 14 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 111 (accept_3_4 13 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 111 (accept_3_4 10 32 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 32 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 111
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 111 (accept_3_4 7 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  111 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 111 (accept_3_4 4 32 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 32 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 111 (accept_3_4 1 32 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 111)))))))))))))))))))))))))))))))) (allB_succ 31 111
  (allA_succ_of_accept 30 31 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 31 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 111 (accept_3_5 29 31 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 111 (Polychromatic418967fa.accept_18_9_13_3_1_5088
  27 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 111 (accept_3_5 26
  31 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 111
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 111 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 31 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 111 (accept_3_5 23 31 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 31 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 111 (Polychromatic418967fa.accept_11_10_9_1_1_2186
  21 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 111 (accept_3_5 20
  31 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 111
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 111 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 31 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 111 (accept_3_5 17 31 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 111 (Polychromatic418967fa.accept_9_6_4_3_1_203 15
  31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 111 (accept_3_5 14 31
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 111
  (Polychromatic418967fa.accept_19_13_12_16_1_5087 13 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 111 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 31 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 111 (accept_3_5 11 31 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 31 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 111
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 111 (accept_3_5 8 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  111 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 111 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 31 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 111 (accept_3_5 5 31 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 111 (Polychromatic418967fa.accept_15_3_1_6_1_206 3
  31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 111 (accept_3_5 2 31 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 111 (Polychromatic418967fa.accept_9_1_4_3_1_201 1
  31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 111)))))))))))))))))))))))))))))))
  (allB_succ 30 111 (allA_succ_of_accept 29 30 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 111
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 30 111 3 9 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 30 111 (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 30 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 111 3 8 10 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 111
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 23 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 30 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 30 111 3 7 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 30 111 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 30 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 111
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 111 3 6 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 111 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 30 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 111 3 5 10 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 111
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 30 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 111 3 4 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 30 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 111
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 30 111 3 3 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 30 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 30 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 111 (Polychromatic418967fa.accept_16_7_14_15_1_2932 7 30 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 111 3 2 10 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 30 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 30 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 30 111 3 1 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 30 111 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 30 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 30 111)))))))))))))))))))))))))))))) (allB_succ 29 111 (allA_succ_of_accept 28 29 111 (accept_3_4 28 29 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 111 (Polychromatic418967fa.accept_13_1_3_7_1_1710
  27 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 111 (accept_3_4 25 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 29 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 111 (accept_3_4 22 29 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 111 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 29 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 111
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 111 (accept_3_4 19 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 111 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 29 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 111 (accept_3_4 16 29 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 29 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 111 (accept_3_4 13 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 111 (Polychromatic418967fa.accept_13_11_3_7_1_2513 11 29 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 111 (accept_3_4 10 29 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 29 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 111
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 111 (accept_3_4 7 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  111 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 29 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 111 (accept_3_4 4 29 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 111 (Polychromatic418967fa.accept_16_3_13_15_1_1913 3 29 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 111 (accept_3_4 1 29 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 111))))))))))))))))))))))))))))) (allB_succ 28 111
  (allA_succ_of_accept 27 28 111 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 28 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 28 111 (accept_3_5 26 28 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 28 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 28 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 24
  28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 111 (accept_3_5 23 28
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 111
  (Polychromatic418967fa.accept_9_4_1_3_1_190 22 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 28 111 (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 28 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 28 111 (accept_3_5 20 28 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 28 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 111 (Polychromatic418967fa.accept_11_7_6_1_1_2182
  18 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 111 (accept_3_5 17
  28 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 111
  (Polychromatic418967fa.accept_9_7_1_3_1_443 16 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 28 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 28 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 28 111 (accept_3_5 14 28 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 28 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 111
  (Polychromatic418967fa.accept_19_12_9_16_1_5086 12 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 28 111 (accept_3_5 11 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  28 111 (Polychromatic418967fa.accept_19_10_9_16_1_5085 10 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 28 111 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 28 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 111 (accept_3_5 8 28 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 28 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 111
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 28 111 (accept_3_5 5 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28
  111 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 28 111 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 28 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 111 (accept_3_5 2 28 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 28 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 111)))))))))))))))))))))))))))) (allB_succ 27 111
  (allA_succ_of_accept 26 27 111 (Polychromatic418967fa.accept_10_6_7_1_1_1297 26 27 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 111 (Polychromatic418967fa.accept_15_10_12_6_1_3000 25 27
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 111 3 8 9 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 111
  (Polychromatic418967fa.accept_16_7_11_15_1_2929 23 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 111 (Polychromatic418967fa.accept_15_7_12_6_1_1327 22 27 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 111 3 7 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 111 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 27 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 111
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 27 111 3 6 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 27 111 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 27 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 111 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 27 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 111 3 5 9 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 111
  (Polychromatic418967fa.accept_10_4_7_1_1_471 14 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 111 (Polychromatic418967fa.accept_17_13_10_9_1_946 13 27 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 111 3 4 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 111 (Polychromatic418967fa.accept_13_11_1_7_1_1691 11 27 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 111
  (Polychromatic418967fa.accept_15_10_12_6_1_3000 10 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 27 111 3 3 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 27 111 (Polychromatic418967fa.accept_13_8_1_7_1_2505 8 27 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 111 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 27 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 111 3 2 9 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 111
  (Polychromatic418967fa.accept_15_5_12_6_1_639 5 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 111 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 27 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 111 3 1 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 111 (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 27 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 111
  (Polychromatic418967fa.accept_16_1_11_15_1_498 1 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 111))))))))))))))))))))))))))) (allB_succ 26 111 (allA_succ_of_accept 25 26 111 (accept_3_4 25 26 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 24
  26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 26 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 26 111 (accept_3_4 22 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  26 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 26 111 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 26 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 111 (accept_3_4 19 26 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 26 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 26 111 (accept_3_4 16 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  26 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 26 111 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 26 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 111 (accept_3_4 13 26 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 111 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 26 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 111 (accept_3_4 10 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  26 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 26 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 26 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 111 (accept_3_4 7 26 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 26 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 26 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 111 (accept_3_4 4 26 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 111 (Polychromatic418967fa.accept_15_3_11_6_1_3083
  3 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 111
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 111 (accept_3_4 1 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  111)))))))))))))))))))))))))) (allB_succ 25 111 (allA_succ_of_accept 24 25 111
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 111 (accept_3_5 23 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 111 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 25 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 111 (accept_3_5 20 25 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 111 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 25 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 111 (accept_3_5 17 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 111 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 25 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 111 (accept_3_5 14 25 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 111 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 25 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 111
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 111 (accept_3_5 11 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 25 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 111 (accept_3_5 8 25 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 111 (Polychromatic418967fa.accept_19_7_6_16_1_3818 7 25 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 111 (accept_3_5 5 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  111 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 25 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 111 (accept_3_5 2 25 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 111 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 25 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 111))))))))))))))))))))))))) (allB_succ 24 111
  (allA_succ_of_accept 23 24 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 24 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 24 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 111 3 7 8 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 111
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 24 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 111 3 6 8 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 111 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 24 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 111
  (Polychromatic418967fa.accept_7_2_3_6_1_4 16 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 111 3 5 8 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 111 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 24 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 24 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 111 3 4 8 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 111
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 24 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 111 3 3 8 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 111 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 24 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 111
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 111 3 2 8 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 111 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 24 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 111 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 24 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 111 3 1 8 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 111
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 111 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 24 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 111)))))))))))))))))))))))) (allB_succ 23 111 (allA_succ_of_accept 22 23
  111 (accept_3_4 22 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 111
  (Polychromatic418967fa.accept_12_9_11_3_1_772 21 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 111 (accept_3_4 19 23 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 23 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 17
  23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 111 (accept_3_4 16 23
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 111 (Polychromatic418967fa.accept_7_1_2_6_1_55
  15 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 111
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 111 (accept_3_4 13 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 111 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 23 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 111 (accept_3_4 10 23 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 111 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 23 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 111
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 111 (accept_3_4 7 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  111 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 111 (Polychromatic418967fa.accept_24_5_23_15_1_5084 5 23 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 111 (accept_3_4 4 23 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 23 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 23
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 111 (accept_3_4 1 23 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 111))))))))))))))))))))))) (allB_succ 22 111
  (allA_succ_of_accept 21 22 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 22 111 (accept_3_5 20 22 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 22 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 22 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 22 111 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  18 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 111 (accept_3_5 17
  22 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 111
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 22 111 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 22 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 111 (accept_3_5 14 22 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 22 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 22 111 (Polychromatic418967fa.accept_7_5_1_6_1_163 12
  22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 111 (accept_3_5 11 22
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 111
  (Polychromatic418967fa.accept_9_1_4_3_1_201 10 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 22 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 111 (accept_3_5 8 22 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 22 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 22 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 111 (Polychromatic418967fa.accept_9_6_4_3_1_203 6
  22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 111 (accept_3_5 5 22 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22 111 (Polychromatic418967fa.accept_13_4_9_7_1_2402 4
  22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 111
  (Polychromatic418967fa.accept_10_3_2_1_1_839 3 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 22 111 (accept_3_5 2 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22
  111 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 111)))))))))))))))))))))) (allB_succ 21 111 (allA_succ_of_accept 20 21 111
  (Polychromatic418967fa.accept_11_9_10_1_1_581 20 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 111 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 21 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 111 3 6 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 111 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 21 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 111
  (Polychromatic418967fa.accept_13_3_8_7_1_4135 16 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 21 111 3 5 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 21 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 111 (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 21
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 111 3 4 7 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 111
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 111 3 3 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 111 (Polychromatic418967fa.accept_14_8_7_13_1_4113 8 21 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 111
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 21 111 3 2 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 21 111 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 21 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 111 (Polychromatic418967fa.accept_16_4_5_15_1_5083 4 21 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 111 3 1 7 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 21 111 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 21 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 21 111))))))))))))))))))))) (allB_succ 20 111 (allA_succ_of_accept 19 20 111
  (accept_3_4 19 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 111
  (Polychromatic418967fa.accept_12_6_8_3_1_82 18 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 111 (accept_3_4 16 20 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 20 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 111 (Polychromatic418967fa.accept_9_5_2_3_1_194 14
  20 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 111 (accept_3_4 13 20
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 111
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 111 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 111 (accept_3_4 10 20 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 111 (Polychromatic418967fa.accept_18_9_2_3_1_5082 9 20 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 111 (Polychromatic418967fa.accept_9_8_2_3_1_447 8
  20 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 111 (accept_3_4 7 20 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 6
  20 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 111 (accept_3_4 4 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  111 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 111 (Polychromatic418967fa.accept_21_2_20_6_1_2277 2 20 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 111 (accept_3_4 1 20 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 111)))))))))))))))))))) (allB_succ 19 111 (allA_succ_of_accept 18 19 111
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 111 (accept_3_5 17 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 19 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 111 (accept_3_5 14 19 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 111 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 19 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 111
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 111 (accept_3_5 11 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 111 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 19 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 111 (accept_3_5 8 19 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 111 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 19 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 111
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 111 (accept_3_5 5 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  111 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 111 (Polychromatic418967fa.accept_21_3_19_6_1_5081 3 19 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 111 (accept_3_5 2 19 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 19 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 111))))))))))))))))))) (allB_succ 18 111 (allA_succ_of_accept 17
  18 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 18 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 18 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 111 3 5 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 111 (Polychromatic418967fa.accept_12_2_6_3_1_331 14
  18 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 111 3 4 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 111 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 18 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 111 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 18 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 111 3 3 6 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 111
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 18 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 111 (Polychromatic418967fa.accept_20_7_18_11_1_5080 7 18 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 111 3 2 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 111
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 18 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 111 3 1 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 18 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 111)))))))))))))))))) (allB_succ 17 111
  (allA_succ_of_accept 16 17 111 (accept_3_4 16 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 111 (accept_3_4 13 17 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 111 (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 17 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 111
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 111 (accept_3_4 10 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 17 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 111 (accept_3_4 7 17 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 17 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 111 (Polychromatic418967fa.accept_9_5_8_3_1_437 5
  17 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 111 (accept_3_4 4 17 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 111 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3
  17 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 111
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 111 (accept_3_4 1 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  111))))))))))))))))) (allB_succ 16 111 (allA_succ_of_accept 15 16 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 16
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 111 (accept_3_5 14 16 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 13
  16 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 111
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 16 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 111 (accept_3_5 11 16 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  16 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 16 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 16 111 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 16 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 111 (accept_3_5 8 16 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 111
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 16 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 111 (accept_3_5 5 16 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16
  111 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 16 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 16 111 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 16 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 111 (accept_3_5 2 16 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 16 111 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 111)))))))))))))))) (allB_succ 15 111 (allA_succ_of_accept 14 15
  111 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 15 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 15 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 111 3 4 5 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 111 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 15 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 111
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 15 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 111 3 3 5 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 111 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 15 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 111 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 15 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 111 3 2 5 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 111
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 15 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 15 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 111 3 1 5 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 15 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 111
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 15 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 111))))))))))))))) (allB_succ 14 111 (allA_succ_of_accept 13 14 111 (accept_3_4 13 14 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 111 (Polychromatic418967fa.accept_17_12_14_9_1_5079 12 14
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 14 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 111 (accept_3_4 10 14 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  14 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 14 111 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 14 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 111 (accept_3_4 7 14 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 14 111 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 14 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 111 (accept_3_4 4 14 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 111 (Polychromatic418967fa.accept_13_3_1_7_1_1706 3
  14 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 111
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 14 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 14 111 (accept_3_4 1 14 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  111)))))))))))))) (allB_succ 13 111 (allA_succ_of_accept 12 13 111 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 13
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 13 111 (accept_3_5 11 13 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  13 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 111
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 13 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 13 111 (accept_3_5 8 13 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13
  111 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 13 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 13 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 111 (accept_3_5 5 13 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 13 111 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 111 (Polychromatic418967fa.accept_11_3_2_1_1_994 3
  13 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 111 (accept_3_5 2 13 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 111 (Polychromatic418967fa.accept_9_1_4_3_1_201 1
  13 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 111))))))))))))) (allB_succ 12 111
  (allA_succ_of_accept 11 12 111 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 12 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 111 (Polychromatic418967fa.accept_13_10_12_7_1_1079 10 12
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 111 3 3 4 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 111
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 12 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 111 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 12 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 111 3 2 4 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 111 (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 12 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 111
  (Polychromatic418967fa.accept_7_4_5_6_1_344 4 12 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 12 111 3 1 4 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 12 111 (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 12 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 111 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 12 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 111)))))))))))) (allB_succ 11 111
  (allA_succ_of_accept 10 11 111 (accept_3_4 10 11 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  11 111 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 11 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 11 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 111 (accept_3_4 7 11 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 11 111 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 11 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 111
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 11 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 11 111 (accept_3_4 4 11 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11
  111 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 11 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 11 111 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 11 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 111 (accept_3_4 1 11 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 11 111))))))))))) (allB_succ 10 111 (allA_succ_of_accept 9 10 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 111 (accept_3_5 8 10 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  111 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 10 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 10 111 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 10 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 111 (accept_3_5 5 10 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 10 111 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 10 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 111 (Polychromatic418967fa.accept_13_3_10_7_1_1061
  3 10 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 111 (accept_3_5 2 10
  111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 111 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  10 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 111)))))))))) (allB_succ 9 111
  (allA_succ_of_accept 8 9 111 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 9 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 111 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 9 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 111 3 2 3 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 111
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 9 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 111 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 9 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 111 3 1 3 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 111
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 9 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 111))))))))) (allB_succ 8 111 (allA_succ_of_accept 7 8 111 (accept_3_4 7 8 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 111 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 8 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 111
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 111 (accept_3_4 4 8 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 111
  (Polychromatic418967fa.accept_10_3_8_1_1_182 3 8 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 111 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 8 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 111 (accept_3_4 1 8 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 111)))))))) (allB_succ 7 111 (allA_succ_of_accept 6 7 111
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 7 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 111 (accept_3_5 5 7 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 111
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 111 (Polychromatic418967fa.accept_16_3_7_15_1_1130 3 7 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 111 (accept_3_5 2 7 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 111 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 7 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 111))))))) (allB_succ 6 111 (allA_succ_of_accept 5 6 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 111 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 6 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 111 3 1 2 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 111 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 6 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 111
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 111)))))) (allB_succ 5 111 (allA_succ_of_accept 4 5 111 (accept_3_4 4 5 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 111 (Polychromatic418967fa.accept_15_3_5_6_1_4005 3 5 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 111 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5
  111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 111 (accept_3_4 1 5 111
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 111))))) (allB_succ 4 111 (allA_succ_of_accept 3 4 111
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 4 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 111 (accept_3_5 2 4 111 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 111
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 111)))) (allB_succ 3 111 (allA_succ_of_accept 2 3 111 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 3 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 111
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 3 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 111))) (allB_succ 2 111 (allA_succ_of_accept 1 2 111 (accept_3_4 1 2 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 111)) (allB_two
  111)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


