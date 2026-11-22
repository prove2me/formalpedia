-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch118
-- name    : Polychromatic418967fa_Branch118
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:11:53.450307+00:00
-- url     : https://prove2.me/theorems/fc426edc-b2b0-455b-b9da-c433d107ebe6
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

def Polychromatic418967fa.branch_118 : allB 118 118 :=
  allB_succ' 2 117 118 (Eq.refl Bool.true) (allA_succ_of_accept 1 117 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  117 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117 118)) (allB_succ' 3 116 118
  (Eq.refl Bool.true) (allA_of_3_1 3 116 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 115 118 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 115 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 118 (accept_3_3 2 115 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 115 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 118)))) (allB_succ' 5 114 118 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 114 118 2 2 57 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 114 118 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 114 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 118 2 1 57 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 114 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 118))))) (allB_succ' 6 113 118 (Eq.refl
  Bool.true) (allA_of_3_1 6 113 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 112 118 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 112 118 2 3 56 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 112 118 (accept_3_3 5 112 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112
  118 2 2 56 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  112 118 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 112 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 112 118 2 1 56 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 112 118 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 112 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 118))))))) (allB_succ' 8 111 118 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 111 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 111 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 118 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 111 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 118 (accept_3_3 5 111 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 118 (Polychromatic418967fa.accept_9_4_3_1_1_154 4
  111 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 118
  (Polychromatic418967fa.accept_10_3_1_8_1_132 3 111 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 111 118 (accept_3_3 2 111 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  111 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 111 118)))))))) (allB_succ' 9 110 118 (Eq.refl Bool.true) (allA_of_3_1 9 110 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 109 118 (Eq.refl Bool.true) (allA_succ_of_accept 9 109 118
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 118 (accept_3_3 8 109 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 118 (Polychromatic418967fa.accept_13_6_5_1_1_834 6 109 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 118 (accept_3_3 5 109 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 118 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 109 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 118
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 118 (accept_3_3 2 109 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 118 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 109 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 118)))))))))) (allB_succ' 11 108 118 (Eq.refl Bool.true) (allA_succ_of_gcd 10 108 118 2 5 54
  59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 118
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 108 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 108 118 2 4 54 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 118 (Polychromatic418967fa.accept_17_7_6_16_1_2195 7 108 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 118 2 3 54 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 118 (accept_3_3 5 108 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 108 118 2 2 54 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 108 118 (Polychromatic418967fa.accept_13_3_4_1_1_363 3 108 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 118 2 1 54 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 118 (Polychromatic418967fa.accept_15_1_3_13_1_2548
  1 108 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108 118))))))))))) (allB_succ' 12 107
  118 (Eq.refl Bool.true) (allA_of_3_1 12 107 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 106 118
  (Eq.refl Bool.true) (allA_succ_of_gcd 12 106 118 2 6 53 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 106 118 (accept_3_3 11 106 118 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 106 118 2 5 53 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 106 118 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 106 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 106 118 2 4 53 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 106 118 (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 106 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 118 2 3 53 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 118 (accept_3_3 5 106 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 106 118 2 2 53 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 106 118 (Polychromatic418967fa.accept_9_3_7_1_1_143 3
  106 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 118 2 1 53 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 118
  (Polychromatic418967fa.accept_18_1_16_10_1_2065 1 106 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 106 118))))))))))))) (allB_succ' 14 105 118 (Eq.refl Bool.true) (allA_succ_of_accept 13 105 118
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 105 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 105 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 118 (accept_3_3 11 105 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 105 118 (Polychromatic418967fa.accept_20_10_5_18_1_5627 10 105 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 118
  (Polychromatic418967fa.accept_18_9_15_10_1_395 9 105 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 118 (accept_3_3 8 105 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  105 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 105 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 118 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 105 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 118 (accept_3_3 5 105 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 118 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 105 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 118
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 105 118 (accept_3_3 2 105 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  105 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 105 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 105 118)))))))))))))) (allB_succ' 15 104 118 (Eq.refl Bool.true) (allA_of_3_1 15 104 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 103 118 (Eq.refl Bool.true) (allA_succ_of_accept 15 103 118
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 118 (accept_3_3 14 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 118 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 103 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 118 (accept_3_3 11 103 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 118 (Polychromatic418967fa.accept_19_10_8_4_1_5626 10 103 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 118
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 118 (accept_3_3 8 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 118 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 118 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 103 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 118 (accept_3_3 5 103 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 118 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 103 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 118
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 118 (accept_3_3 2 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 118)))))))))))))))) (allB_succ' 17 102 118 (Eq.refl Bool.true) (allA_succ_of_gcd 16 102 118
  2 8 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102
  118 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 102 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 102 118 2 7 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 102 118 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 102 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 118 2 6 51 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 118 (accept_3_3 11 102 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 118 2 5 51 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 118
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 102 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 118 2 4 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 118 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 102 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 118 2 3 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 118 (accept_3_3 5 102 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 118 2 2 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 102 118 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 102 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 118 2 1 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 118 (Polychromatic418967fa.accept_15_1_12_13_1_944
  1 102 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 118))))))))))))))))) (allB_succ'
  18 101 118 (Eq.refl Bool.true) (allA_of_3_1 18 101 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 100 118
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 100 118 2 9 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 100 118 (accept_3_3 17 100 118 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 100 118 2 8 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 100 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 100 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 100 118 2 7 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 100 118 (Polychromatic418967fa.accept_12_1_4_10_1_209
  13 100 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 118 2 6 50 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 118
  (accept_3_3 11 100 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 118 2 5 50 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 118
  (Polychromatic418967fa.accept_19_9_5_4_1_1866 9 100 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 100 118 2 4 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 100 118 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 100 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 118 2 3 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 100 118 (accept_3_3 5 100 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 100 118 2 2 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 100 118 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 100 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 118 2 1 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 1
  100 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 118))))))))))))))))))) (allB_succ'
  20 99 118 (Eq.refl Bool.true) (allA_succ_of_accept 19 99 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 118
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 99 118 (accept_3_3 17 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  99 118 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 99 118 (Polychromatic418967fa.accept_17_15_14_16_1_5625 15 99 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 118 (accept_3_3 14 99 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 99 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 118
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 99 118 (accept_3_3 11 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  99 118 (Polychromatic418967fa.accept_22_10_11_8_1_5624 10 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 99 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 118 (accept_3_3 8 99 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 118
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 118 (accept_3_3 5 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99
  118 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 99 118 (Polychromatic418967fa.accept_15_3_9_13_1_1681 3 99 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 118 (accept_3_3 2 99 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 99 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 118)))))))))))))))))))) (allB_succ' 21 98 118 (Eq.refl
  Bool.true) (allA_of_3_1 21 98 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 97 118 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 97 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 118 (accept_3_3 20 97 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 97 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 97 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 118 (Polychromatic418967fa.accept_13_5_6_1_1_822
  18 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 118 (accept_3_3 17
  97 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 118
  (Polychromatic418967fa.accept_12_4_1_10_1_221 16 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 97 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 97 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 118 (accept_3_3 14 97 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 97 118 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 97 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 118 (Polychromatic418967fa.accept_9_3_7_1_1_143 12
  97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 118 (accept_3_3 11 97
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 118
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 97 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 118 (accept_3_3 8 97 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 97 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 97 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 118 (Polychromatic418967fa.accept_9_6_7_1_1_145 6
  97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 118 (accept_3_3 5 97 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 118 (Polychromatic418967fa.accept_9_4_7_1_1_379 4
  97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 118
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 118 (accept_3_3 2 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  118 (Polychromatic418967fa.accept_17_1_12_16_1_2211 1 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 97 118)))))))))))))))))))))) (allB_succ' 23 96 118 (Eq.refl Bool.true) (allA_succ_of_gcd 22 96
  118 2 11 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  96 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 96 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 96 118 2 10 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 96 118 (Polychromatic418967fa.accept_13_6_5_1_1_834 19 96 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 118 2 9 48 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 118 (accept_3_3 17 96 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 118 2 8 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 118 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 96 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 118 2 7 48 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 118
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 96 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 118 2 6 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 118 (accept_3_3 11 96 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96
  118 2 5 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  96 118 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 96 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 96 118 2 4 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 96 118 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 96 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 118 2 3 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 118 (accept_3_3 5 96 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 118 2 2 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 96 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 96 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 118 2 1 48 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 118
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 96 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 118))))))))))))))))))))))) (allB_succ' 24 95 118 (Eq.refl Bool.true) (allA_of_3_1 24 95 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 94 118 (Eq.refl Bool.true) (allA_succ_of_gcd 24 94 118 2 12 47 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 94 118
  (accept_3_3 23 94 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94 118 2 11 47 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 94 118
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 94 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 94 118 2 10 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 94 118 (Polychromatic418967fa.accept_10_9_4_8_1_741 19 94 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 94 118 2 9 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 94 118 (accept_3_3 17 94 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 94 118 2 8 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 94 118 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 94 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 94 118 2 7 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 118 (Polychromatic418967fa.accept_17_13_9_16_1_3254
  13 94 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 118 2 6 47 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 118 (accept_3_3 11
  94 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 118 2 5 47 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 118
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 94 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 118 2 4 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 118 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 94 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 118 2 3 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 118 (accept_3_3 5 94 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 118 2 2 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 118 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 94 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 118 2 1 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 118 (Polychromatic418967fa.accept_21_1_10_13_1_5623
  1 94 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 118)))))))))))))))))))))))))
  (allB_succ' 26 93 118 (Eq.refl Bool.true) (allA_succ_of_accept 25 93 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 25
  93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 118
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 93 118 (accept_3_3 23 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  93 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 93 118 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 93 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 118 (accept_3_3 20 93 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 93 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 118
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 93 118 (accept_3_3 17 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  93 118 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 93 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 118 (accept_3_3 14 93 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 118
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 93 118 (accept_3_3 11 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  93 118 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 93 118 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 93 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 118 (accept_3_3 8 93 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 118
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 118 (accept_3_3 5 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93
  118 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 93 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 118 (accept_3_3 2 93 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 93 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 118)))))))))))))))))))))))))) (allB_succ' 27 92 118 (Eq.refl
  Bool.true) (allA_of_3_1 27 92 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 91 118 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 91 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 118 (accept_3_3 26 91 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 91 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 91 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 118 (Polychromatic418967fa.accept_17_7_6_16_1_2195
  24 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 118 (accept_3_3 23
  91 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 118
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 22 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 91 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 91 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 118 (accept_3_3 20 91 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 91 118 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 91 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 118 (Polychromatic418967fa.accept_15_3_1_13_1_1672
  18 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 118 (accept_3_3 17
  91 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 118
  (Polychromatic418967fa.accept_11_5_3_8_1_454 16 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 91 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 118 (accept_3_3 14 91 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 91 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 91 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 118
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 12 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 118 (accept_3_3 11 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 118 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 118 (accept_3_3 8 91 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 118 (Polychromatic418967fa.accept_17_7_6_16_1_2195 7 91 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 118
  (Polychromatic418967fa.accept_11_6_3_8_1_843 6 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 118 (accept_3_3 5 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  118 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 118 (accept_3_3 2 91 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 118)))))))))))))))))))))))))))) (allB_succ' 29 90 118
  (Eq.refl Bool.true) (allA_succ_of_gcd 28 90 118 2 14 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 90 118 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 90 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 118 2 13 45 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 118
  (Polychromatic418967fa.accept_20_5_10_18_1_5622 25 90 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 118 2 12 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 90 118 (accept_3_3 23 90 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90
  118 2 11 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  90 118 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 90 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 90 118 2 10 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 90 118 (Polychromatic418967fa.accept_17_2_5_16_1_1264 19 90 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 118 2 9 45 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 118 (accept_3_3 17 90 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 118 2 8 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 118 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 90 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 118 2 7 45 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 118
  (Polychromatic418967fa.accept_19_13_14_4_1_5621 13 90 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 90 118 2 6 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 90 118 (accept_3_3 11 90 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90
  118 2 5 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  90 118 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 90 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 90 118 2 4 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 90 118 (Polychromatic418967fa.accept_19_7_14_4_1_4268 7 90 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 118 2 3 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 118 (accept_3_3 5 90 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 118 2 2 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 90 118 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 90 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 118 2 1 45 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 118
  (Polychromatic418967fa.accept_17_1_5_16_1_5589 1 90 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 118))))))))))))))))))))))))))))) (allB_succ' 30 89 118 (Eq.refl Bool.true) (allA_of_3_1 30 89 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 88 118 (Eq.refl Bool.true) (allA_succ_of_gcd 30 88 118 2 15 44
  59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 88 118
  (accept_3_3 29 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88 118 2 14 44 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 88 118
  (Polychromatic418967fa.accept_19_8_12_4_1_2981 27 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 88 118 2 13 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 88 118 (Polychromatic418967fa.accept_12_1_4_10_1_209 25 88 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 88 118 2 12 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 88 118 (accept_3_3 23 88 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88 118 2 11 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 88 118 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 88 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 88 118 2 10 44 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 88 118
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 88 118 2 9 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 88 118 (accept_3_3 17 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88
  118 2 8 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  88 118 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 88 118 2 7 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 88 118 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 88 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 118 2 6 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 118 (accept_3_3 11 88 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88 118 2 5 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 88 118 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 88 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 88 118 2 4 44 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 118
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 88 118 2 3 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 88 118 (accept_3_3 5 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 118
  2 2 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88
  118 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 88 118 2 1 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 88 118 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 88 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 88 118))))))))))))))))))))))))))))))) (allB_succ' 32 87 118 (Eq.refl
  Bool.true) (allA_succ_of_accept 31 87 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 118 (Polychromatic418967fa.accept_7_2_3_6_1_4 30
  87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 118 (accept_3_3 29 87
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 118
  (Polychromatic418967fa.accept_13_2_9_1_1_67 28 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 87 118 (Polychromatic418967fa.accept_18_9_15_10_1_395 27 87 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 118 (accept_3_3 26 87 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 87 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 87 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 118 (Polychromatic418967fa.accept_13_11_9_1_1_1407
  24 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 118 (accept_3_3 23
  87 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 118
  (Polychromatic418967fa.accept_9_4_6_1_1_393 22 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 87 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 118 (accept_3_3 20 87 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 87 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 118 (Polychromatic418967fa.accept_7_4_3_6_1_340 18
  87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 118 (accept_3_3 17 87
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 118 (Polychromatic418967fa.accept_7_2_3_6_1_4
  16 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 118
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 118 (accept_3_3 14 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 87 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 118 (accept_3_3 11 87 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 118 (Polychromatic418967fa.accept_13_10_9_1_1_5609 10 87 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 118
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 118 (accept_3_3 8 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  118 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 118 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 87 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 118 (accept_3_3 5 87 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 118 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 87 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 87
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 118 (accept_3_3 2 87 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 118))))))))))))))))))))))))))))))))
  (allB_succ' 33 86 118 (Eq.refl Bool.true) (allA_of_3_1 33 86 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  34 85 118 (Eq.refl Bool.true) (allA_succ_of_accept 33 85 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 118 (accept_3_3 32 85 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 118
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 118 (accept_3_3 29 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 118 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 85 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 118 (accept_3_3 26 85 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 118 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 85 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 118
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 118 (accept_3_3 23 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 118 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 118 (accept_3_3 20 85 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 85 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 118
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 118 (accept_3_3 17 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 118 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 85 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 118 (accept_3_3 14 85 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 118 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 85 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 118
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 118 (accept_3_3 11 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 118 (Polychromatic418967fa.accept_19_10_9_4_1_5620 10 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 118 (accept_3_3 8 85 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 118
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 118 (accept_3_3 5 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  118 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 85 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 118 (accept_3_3 2 85 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 118 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 85 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 118)))))))))))))))))))))))))))))))))) (allB_succ' 35
  84 118 (Eq.refl Bool.true) (allA_succ_of_gcd 34 84 118 2 17 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 118 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 84 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 118 2 16 42 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 118
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 84 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 118 2 15 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 118 (accept_3_3 29 84 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84
  118 2 14 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  84 118 (Polychromatic418967fa.accept_16_11_4_6_1_4422 27 84 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 84 118 2 13 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 84 118 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 84 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 118 2 12 42 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 118 (accept_3_3 23 84 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 118 2 11 42 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 118
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 84 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 118 2 10 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 118 (Polychromatic418967fa.accept_10_9_4_8_1_741 19 84 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 118 2 9 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 118 (accept_3_3 17 84 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 84 118 2 8 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 84 118 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 84 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 118 2 7 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 118 (Polychromatic418967fa.accept_9_4_3_1_1_154 13
  84 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 118 2 6 42 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 118 (accept_3_3 11
  84 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 118 2 5 42 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 118
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 84 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 118 2 4 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 118 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 84 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 118 2 3 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 118 (accept_3_3 5 84 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 84 118 2 2 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 84 118 (Polychromatic418967fa.accept_13_3_6_1_1_3797 3 84 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 118 2 1 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 118 (Polychromatic418967fa.accept_22_1_18_8_1_5619 1
  84 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  118))))))))))))))))))))))))))))))))))) (allB_succ' 36 83 118 (Eq.refl Bool.true) (allA_of_3_1 36 83 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 82 118 (Eq.refl Bool.true) (allA_succ_of_gcd 36 82 118 2 18 41 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 82 118
  (accept_3_3 35 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82 118 2 17 41 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 82 118
  (Polychromatic418967fa.accept_16_1_2_6_1_2295 33 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 82 118 2 16 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 82 118 (Polychromatic418967fa.accept_13_5_4_1_1_364 31 82 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 82 118 2 15 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 82 118 (accept_3_3 29 82 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82 118 2 14 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 82 118 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 82
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 82 118 2 13 41 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 82 118
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 82 118 2 12 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 82 118 (accept_3_3 23 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82
  118 2 11 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  82 118 (Polychromatic418967fa.accept_15_6_7_13_1_1666 21 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 82 118 2 10 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 82 118 (Polychromatic418967fa.accept_16_3_2_6_1_4461 19 82 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 118 2 9 41 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 118 (accept_3_3 17 82 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82 118 2 8 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 82 118 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 82 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 118 2 7 41 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 118
  (Polychromatic418967fa.accept_11_2_5_8_1_470 13 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 82 118 2 6 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 82 118 (accept_3_3 11 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82
  118 2 5 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  82 118 (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 82 118 2 4 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 82 118 (Polychromatic418967fa.accept_20_7_2_18_1_5618 7 82 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 118 2 3 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 118 (accept_3_3 5 82 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 118 2 2 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 82 118 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 82 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 118 2 1 41 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 118
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 82 118))))))))))))))))))))))))))))))))))))) (allB_succ' 38 81 118 (Eq.refl Bool.true) (allA_succ_of_accept
  37 81 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 118 (Polychromatic418967fa.accept_20_16_1_18_1_5617 36 81 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 118 (accept_3_3 35 81 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 118 (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 81 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 118
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 118 (accept_3_3 32 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 118 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 81 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 118 (accept_3_3 29 81 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 118 (Polychromatic418967fa.accept_13_2_3_1_1_3823 28 81 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 118
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 118 (accept_3_3 26 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 118 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 81 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 118 (accept_3_3 23 81 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 118 (Polychromatic418967fa.accept_15_7_6_13_1_936 22 81 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 118
  (Polychromatic418967fa.accept_16_5_1_6_1_3367 21 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 118 (accept_3_3 20 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 118 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 81 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 118 (accept_3_3 17 81 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 118 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 81 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 118
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 118 (accept_3_3 14 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 118 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 81 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 118 (accept_3_3 11 81 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 118 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 81 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 118
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 118 (accept_3_3 8 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 118 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 81 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 118 (accept_3_3 5 81 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 118 (Polychromatic418967fa.accept_13_4_3_1_1_2898 4 81 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 118 (accept_3_3 2 81 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  118)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 80 118 (Eq.refl Bool.true) (allA_of_3_1 39 80 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 79 118 (Eq.refl Bool.true) (allA_succ_of_accept 39 79 118
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 118 (accept_3_3 38 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 118 (accept_3_3 35 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 118 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 79 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 118
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 118 (accept_3_3 32 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 118 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 118 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 118 (accept_3_3 29 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 118 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 79 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 118
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 118 (accept_3_3 26 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 118 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 118 (accept_3_3 23 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 79 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 118
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 118 (accept_3_3 20 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 118 (Polychromatic418967fa.accept_21_19_16_13_1_4099 19 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 118 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 118 (accept_3_3 17 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 118 (Polychromatic418967fa.accept_11_5_2_8_1_866 16 79 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 118
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 118 (accept_3_3 14 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 118 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 118 (accept_3_3 11 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 118 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 79 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 118
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 118 (accept_3_3 8 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  118 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 118 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 118 (accept_3_3 5 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 118 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 79 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 118
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 118 (accept_3_3 2 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 118)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 78 118 (Eq.refl Bool.true) (allA_succ_of_gcd
  40 78 118 2 20 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 78 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 78 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 118 2 19 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 118 (Polychromatic418967fa.accept_7_2_1_6_1_173 37
  78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 118 2 18 39 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 118 (accept_3_3 35
  78 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 118 2 17 39 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 118
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 118 2 16 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 78 118 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 78 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 118 2 15 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 118 (accept_3_3 29 78 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 118 2 14 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 118 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 78 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 118 2 13 39 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 118
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 118 2 12 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 118 (accept_3_3 23 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78
  118 2 11 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  78 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 78 118 2 10 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 78 118 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 78 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 118 2 9 39 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 118 (accept_3_3 17 78 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 118 2 8 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 118 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 78 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 118 2 7 39 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 118
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 118 2 6 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 118 (accept_3_3 11 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78
  118 2 5 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  78 118 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 78 118 2 4 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 78 118 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 78 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 118 2 3 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 118 (accept_3_3 5 78 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 118 2 2 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 78 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 78 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 118 2 1 39 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 118
  (Polychromatic418967fa.accept_15_1_3_13_1_2548 1 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 118))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 77 118 (Eq.refl Bool.true) (allA_of_3_1 42 77
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 76 118 (Eq.refl Bool.true) (allA_succ_of_gcd 42 76 118 2
  21 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76
  118 (accept_3_3 41 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 118 2 20 38 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 118
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 118 2 19 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 76 118 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 76 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 118 2 18 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 118 (accept_3_3 35 76 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76 118 2 17 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 76 118 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 76 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 118 2 16 38 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 118
  (Polychromatic418967fa.accept_11_9_10_8_1_444 31 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 118 2 15 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 76 118 (accept_3_3 29 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76
  118 2 14 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  76 118 (Polychromatic418967fa.accept_15_12_1_13_1_3444 27 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 76 118 2 13 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 76 118 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 76 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 118 2 12 38 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 118 (accept_3_3 23 76 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 118 2 11 38 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 118
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 76 118 2 10 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 76 118 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 76 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 118 2 9 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 118 (accept_3_3 17 76 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 76 118 2 8 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 76 118 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 76 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 118 2 7 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 118 (Polychromatic418967fa.accept_10_3_6_8_1_1169
  13 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 118 2 6 38 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 118 (accept_3_3 11
  76 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 118 2 5 38 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 118
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 76 118 2 4 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 76 118 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 76 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 118 2 3 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 118 (accept_3_3 5 76 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 76 118 2 2 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 76 118 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 76 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 118 2 1 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 118 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  118))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 75 118 (Eq.refl Bool.true) (allA_succ_of_accept 43 75
  118 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 118 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 75 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 118 (accept_3_3 41 75 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 75 118 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 75 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 118 (Polychromatic418967fa.accept_7_4_5_6_1_344 39
  75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 118 (accept_3_3 38 75
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 118 (Polychromatic418967fa.accept_4_1_3_2_1_3
  37 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 118
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 118 (accept_3_3 35 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  75 118 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 118 (accept_3_3 32 75 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 75 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 118
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 118 (accept_3_3 29 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 118 (Polychromatic418967fa.accept_22_6_9_8_1_5616 28 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 118 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 75 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 118 (accept_3_3 26 75 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 75 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 118
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 118 (accept_3_3 23 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 118 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 118 (accept_3_3 20 75 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 118
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 118 (accept_3_3 17 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 118 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 118 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 75 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 118 (accept_3_3 14 75 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 118
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 118 (accept_3_3 11 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 118 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 118 (accept_3_3 8 75 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 118
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 118 (accept_3_3 5 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  118 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 118 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 75 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 118 (accept_3_3 2 75 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 118)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45
  74 118 (Eq.refl Bool.true) (allA_of_3_1 45 74 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 73 118
  (Eq.refl Bool.true) (allA_succ_of_accept 45 73 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 118 (accept_3_3 44 73 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 73 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 118
  (Polychromatic418967fa.accept_20_2_13_18_1_5615 42 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 118 (accept_3_3 41 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 118 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 118 (accept_3_3 38 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 118 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 73 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 118
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 118 (accept_3_3 35 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 118 (Polychromatic418967fa.accept_16_2_9_6_1_4441 34 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 118 (accept_3_3 32 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 73 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 118
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 118 (accept_3_3 29 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 118 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 118 (accept_3_3 26 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 118 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 73 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 118
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 118 (accept_3_3 23 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 118 (Polychromatic418967fa.accept_13_9_8_1_1_824 22 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 118 (accept_3_3 20 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 118
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 118 (accept_3_3 17 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 118 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 118 (accept_3_3 14 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 118 (Polychromatic418967fa.accept_16_13_9_6_1_2306 13 73 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 118
  (Polychromatic418967fa.accept_13_12_8_1_1_825 12 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 118 (accept_3_3 11 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 118 (Polychromatic418967fa.accept_14_10_3_6_1_2728 10 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 118 (accept_3_3 8 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 118
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 118 (accept_3_3 5 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  118 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 118 (accept_3_3 2 73 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 118 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 118)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47
  72 118 (Eq.refl Bool.true) (allA_succ_of_gcd 46 72 118 2 23 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 118 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 72 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 118 2 22 36 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 118
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 118 2 21 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 72 118 (accept_3_3 41 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72
  118 2 20 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  72 118 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 72 118 2 19 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 72 118 (Polychromatic418967fa.accept_13_11_7_1_1_1386 37 72 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 118 2 18 36 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 118 (accept_3_3 35 72 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 118 2 17 36 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 118
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 33 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 118 2 16 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 118 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 72 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 118 2 15 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 118 (accept_3_3 29 72 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 118 2 14 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 118 (Polychromatic418967fa.accept_19_8_15_4_1_2953 27 72 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 118 2 13 36 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 118
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 118 2 12 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 118 (accept_3_3 23 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72
  118 2 11 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  72 118 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 72 118 2 10 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 72 118 (Polychromatic418967fa.accept_13_6_7_1_1_335 19 72 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 118 2 9 36 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 118 (accept_3_3 17 72 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 118 2 8 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 72 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 118 2 7 36 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 118
  (Polychromatic418967fa.accept_19_13_15_4_1_5614 13 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 72 118 2 6 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 72 118 (accept_3_3 11 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72
  118 2 5 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  72 118 (Polychromatic418967fa.accept_19_9_15_4_1_5613 9 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 72 118 2 4 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 72 118 (Polychromatic418967fa.accept_21_7_9_13_1_5612 7 72 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 118 2 3 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 118 (accept_3_3 5 72 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 118 2 2 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 72 118 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 72 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 118 2 1 36 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 118
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 118))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 71 118 (Eq.refl Bool.true) (allA_of_3_1
  48 71 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 70 118 (Eq.refl Bool.true) (allA_succ_of_gcd 48 70
  118 2 24 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  70 118 (accept_3_3 47 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 118 2 23 35 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 70 118
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 70 118 2 22 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 70 118 (Polychromatic418967fa.accept_13_4_5_1_1_833 43 70 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 118 2 21 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 118 (accept_3_3 41 70 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70 118 2 20 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 70 118 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 70 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 70 118 2 19 35 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 70 118
  (Polychromatic418967fa.accept_18_1_16_10_1_2065 37 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 70 118 2 18 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 70 118 (accept_3_3 35 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 70
  118 2 17 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  70 118 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 70 118 2 16 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 70 118 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 70 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 118 2 15 35 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 118 (accept_3_3 29 70 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 118 2 14 35 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 118
  (Polychromatic418967fa.accept_15_12_10_13_1_4497 27 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 70 118 2 13 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 70 118 (Polychromatic418967fa.accept_13_12_5_1_1_1383 25 70 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 70 118 2 12 35 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 118 (accept_3_3 23 70 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 118 2 11 35 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 70 118
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 70 118 2 10 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 70 118 (Polychromatic418967fa.accept_13_6_5_1_1_834 19 70 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 118 2 9 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 118 (accept_3_3 17 70 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 70 118 2 8 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 70 118 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 70 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 118 2 7 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 118 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 118 2 6 35 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 118 (accept_3_3 11
  70 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 118 2 5 35 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 118
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 70 118 2 4 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 70 118 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 70 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 118 2 3 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 118 (accept_3_3 5 70 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 70 118 2 2 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 70 118 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 70 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 118 2 1 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 118 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1
  70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  118))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 69 118 (Eq.refl Bool.true) (allA_succ_of_accept 49
  69 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 118 (accept_3_3 47 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 118 (Polychromatic418967fa.accept_17_12_1_16_1_4360 46 69 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 118
  (Polychromatic418967fa.accept_18_9_15_10_1_395 45 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 118 (accept_3_3 44 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 118 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 118 (accept_3_3 41 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 118 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 69 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 118
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 118 (accept_3_3 38 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 118 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 69 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 118 (accept_3_3 35 69 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 118 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 69 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 118
  (Polychromatic418967fa.accept_14_5_13_6_1_3574 33 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 118 (accept_3_3 32 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 118 (accept_3_3 29 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 118 (Polychromatic418967fa.accept_11_6_3_8_1_843 28 69 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 118
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 118 (accept_3_3 26 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 118 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 118 (accept_3_3 23 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 118 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 69 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 118
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 118 (accept_3_3 20 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 118 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 118 (accept_3_3 17 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 118 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 69 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 118
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 118 (accept_3_3 14 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 118 (accept_3_3 11 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 118 (Polychromatic418967fa.accept_13_10_4_1_1_2142 10 69 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 118
  (Polychromatic418967fa.accept_18_9_15_10_1_395 9 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 118 (accept_3_3 8 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 118 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 69 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 118 (accept_3_3 5 69 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 118 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 118 (accept_3_3 2 69 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  118)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 68 118 (Eq.refl Bool.true) (allA_of_3_1 51 68 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 67 118 (Eq.refl Bool.true) (allA_succ_of_accept 51 67 118
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 67 118 (accept_3_3 50 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  67 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 67 118 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 67 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 67 118 (accept_3_3 47 67 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 67 118 (Polychromatic418967fa.accept_19_8_10_4_1_4292 46 67 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 67 118
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 67 118 (accept_3_3 44 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  67 118 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 67 118 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 67 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 67 118 (accept_3_3 41 67 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 67 118 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 67 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 67 118
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 67 118 (accept_3_3 38 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  67 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 67 118 (Polychromatic418967fa.accept_15_6_7_13_1_1666 36 67 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 67 118 (accept_3_3 35 67 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 67 118 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 67 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 67 118
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 67 118 (accept_3_3 32 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  67 118 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 67 118 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 67 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 67 118 (accept_3_3 29 67 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 67 118 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 67 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 118
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 67 118 (accept_3_3 26 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  67 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 67 118 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 67 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 67 118 (accept_3_3 23 67 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 67 118 (Polychromatic418967fa.accept_13_9_2_1_1_813 22 67 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 118
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 67 118 (accept_3_3 20 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  67 118 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 67 118 (Polychromatic418967fa.accept_16_2_3_6_1_3372 18 67 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 118 (accept_3_3 17 67 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 118 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 67 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 118
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 118 (accept_3_3 14 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  67 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 67 118 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 67 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 118 (accept_3_3 11 67 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 118 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 67 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 118
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 118 (accept_3_3 8 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67
  118 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 67 118 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 67 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 118 (accept_3_3 5 67 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 67 118 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 67 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 118 (accept_3_3 2 67 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  118)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 66 118 (Eq.refl Bool.true) (allA_succ_of_gcd 52
  66 118 2 26 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  51 66 118 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 66 118 2 25 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 66 118 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 66 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 118 2 24 33 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 118 (accept_3_3 47 66 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 118 2 23 33 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 118
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 118 2 22 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 118 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 66 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 118 2 21 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 118 (accept_3_3 41 66 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 118 2 20 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 118 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 66 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 118 2 19 33 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 118
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 118 2 18 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 118 (accept_3_3 35 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66
  118 2 17 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  66 118 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 66 118 2 16 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 66 118 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 66 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 118 2 15 33 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 118 (accept_3_3 29 66 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 118 2 14 33 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 118
  (Polychromatic418967fa.accept_12_3_6_10_1_576 27 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 118 2 13 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 118 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 66 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 118 2 12 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 118 (accept_3_3 23 66 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 118 2 11 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 118 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 66 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 118 2 10 33 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 118
  (Polychromatic418967fa.accept_15_4_6_13_1_956 19 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 118 2 9 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 118 (accept_3_3 17 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66
  118 2 8 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  66 118 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 66 118 2 7 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 66 118 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 66 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 118 2 6 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 118 (accept_3_3 11 66 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 118 2 5 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 66 118 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 66 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 118 2 4 33 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 118
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 118 2 3 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 118 (accept_3_3 5 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 118
  2 2 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66
  118 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 66 118 2 1 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 66 118 (Polychromatic418967fa.accept_16_1_2_6_1_2295 1 66 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66 118)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 54 65 118 (Eq.refl Bool.true) (allA_of_3_1 54 65 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  55 64 118 (Eq.refl Bool.true) (allA_succ_of_gcd 54 64 118 2 27 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 118 (accept_3_3 53 64 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 64 118 2 26 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 64 118 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 64 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 118 2 25 32 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 118
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 118 2 24 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 64 118 (accept_3_3 47 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64
  118 2 23 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  64 118 (Polychromatic418967fa.accept_22_1_20_8_1_4017 45 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 64 118 2 22 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 64 118 (Polychromatic418967fa.accept_11_10_9_8_1_1974 43 64 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 118 2 21 32 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 118 (accept_3_3 41 64 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 118 2 20 32 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 118
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 64 118 2 19 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 64 118 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 64 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 64 118 2 18 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 64 118 (accept_3_3 35 64 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64 118 2 17 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 64 118 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 64 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 118 2 16 32 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 118
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 118 2 15 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 64 118 (accept_3_3 29 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64
  118 2 14 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  64 118 (Polychromatic418967fa.accept_31_27_2_25_1_5611 27 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 64 118 2 13 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 64 118 (Polychromatic418967fa.accept_12_1_4_10_1_209 25 64 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 118 2 12 32 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 118 (accept_3_3 23 64 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 118 2 11 32 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 118
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 64 118 2 10 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 64 118 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 64 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 118 2 9 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 118 (accept_3_3 17 64 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 64 118 2 8 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 64 118 (Polychromatic418967fa.accept_13_2_12_1_1_343 15 64 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 118 2 7 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 118 (Polychromatic418967fa.accept_12_1_4_10_1_209
  13 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 118 2 6 32 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 118 (accept_3_3 11
  64 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 118 2 5 32 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 64 118
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 64 118 2 4 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 64 118 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 64 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 118 2 3 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 118 (accept_3_3 5 64 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 64 118 2 2 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 64 118 (Polychromatic418967fa.accept_17_3_13_16_1_2183 3 64 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 118 2 1 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 118 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  118))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 63 118 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 63 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 63 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 118 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 63 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 118 (accept_3_3 53 63 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 118
  (Polychromatic418967fa.accept_17_1_12_16_1_2211 52 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 63 118 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 63 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 118 (accept_3_3 50 63 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 63 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 63 118 (Polychromatic418967fa.accept_13_9_11_1_1_1375
  48 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 118 (accept_3_3 47
  63 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 118
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 63 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 118 (accept_3_3 44 63 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 63 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 63 118 (Polychromatic418967fa.accept_12_6_3_10_1_224
  42 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 118 (accept_3_3 41
  63 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 118
  (Polychromatic418967fa.accept_15_10_3_13_1_4480 40 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 63 118 (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 63 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 118 (accept_3_3 38 63 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 63 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 118 (Polychromatic418967fa.accept_10_6_3_8_1_1660
  36 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 118 (accept_3_3 35
  63 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 118
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 34 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 63 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 118 (accept_3_3 32 63 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 63 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 118 (Polychromatic418967fa.accept_12_6_3_10_1_224
  30 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 118 (accept_3_3 29
  63 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 118
  (Polychromatic418967fa.accept_17_11_12_16_1_3219 28 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 63 118 (Polychromatic418967fa.accept_14_13_7_6_1_3525 27 63 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 118 (accept_3_3 26 63 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 118
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 63 118 (accept_3_3 23 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  63 118 (Polychromatic418967fa.accept_13_9_11_1_1_1375 22 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 63 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 118 (accept_3_3 20 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 118
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 63 118 (accept_3_3 17 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  63 118 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 63 118 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 118 (accept_3_3 14 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 118
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 63 118 (accept_3_3 11 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  63 118 (Polychromatic418967fa.accept_13_10_11_1_1_2152 10 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 63 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 118 (accept_3_3 8 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 118
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 118 (accept_3_3 5 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63
  118 (Polychromatic418967fa.accept_27_4_9_10_1_5610 4 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 118 (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 118 (accept_3_3 2 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  118)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 62 118 (Eq.refl Bool.true) (allA_of_3_1 57
  62 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 61 118 (Eq.refl Bool.true) (allA_succ_of_accept 57 61
  118 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 61 118 (accept_3_3 56 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  61 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 61 118 (Polychromatic418967fa.accept_13_2_9_1_1_67 54 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 61 118 (accept_3_3 53 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 61 118 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 61 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 61 118
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 61 118 (accept_3_3 50 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  61 118 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 61 118 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 61 118 (accept_3_3 47 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 61 118 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 61 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 61 118
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 61 118 (accept_3_3 44 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  61 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 61 118 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 61 118 (accept_3_3 41 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 61 118 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 61 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 61 118
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 61 118 (accept_3_3 38 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  61 118 (Polychromatic418967fa.accept_13_11_9_1_1_1407 37 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 61 118 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 61 118 (accept_3_3 35 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 61 118 (Polychromatic418967fa.accept_13_8_9_1_1_2147 34 61 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 61 118
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 61 118 (accept_3_3 32 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  61 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 61 118 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 61 118 (accept_3_3 29 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 61 118 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 61 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 61 118
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 61 118 (accept_3_3 26 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  61 118 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 61 118 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 61 118 (accept_3_3 23 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 61 118 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 61 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 61 118
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 61 118 (accept_3_3 20 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  61 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 61 118 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 118 (accept_3_3 17 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 61 118 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 61 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 118
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 61 118 (accept_3_3 14 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  61 118 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 61 118 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 61 118 (accept_3_3 11 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 61 118 (Polychromatic418967fa.accept_13_10_9_1_1_5609 10 61 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 118
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 61 118 (accept_3_3 8 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61
  118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 61 118 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 61 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 118 (accept_3_3 5 61 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 61 118 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 118 (accept_3_3 2 61 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 118 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 61
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  118)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 60 118 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 60 118 2 29 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 60 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 118 2 28 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 118 (Polychromatic418967fa.accept_23_9_14_3_1_5608
  55 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 118 2 27 30 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 118 (accept_3_3 53
  60 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 118 2 26 30 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 118
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 118 2 25 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 118 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 60 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 118 2 24 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 118 (accept_3_3 47 60 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 118 2 23 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 118 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 60 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 118 2 22 30 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 118
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 118 2 21 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 118 (accept_3_3 41 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60
  118 2 20 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  60 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 60 118 2 19 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 60 118 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 60 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 118 2 18 30 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 118 (accept_3_3 35 60 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 118 2 17 30 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 118
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 118 2 16 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 118 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 60 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 118 2 15 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 118 (accept_3_3 29 60 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 118 2 14 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 60 118 (Polychromatic418967fa.accept_17_10_9_16_1_5607 27 60
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 118 2 13 30 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 118
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 118 2 12 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 60 118 (accept_3_3 23 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60
  118 2 11 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  60 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 60 118 2 10 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 60 118 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 60 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 118 2 9 30 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 118 (accept_3_3 17 60 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 118 2 8 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 60 118 (Polychromatic418967fa.accept_18_15_6_10_1_5590 15 60
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 118 2 7 30 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 118
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 118 2 6 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 118 (accept_3_3 11 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60
  118 2 5 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  60 118 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 60 118 2 4 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 60 118 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 60 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 118 2 3 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 118 (accept_3_3 5 60 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 118 2 2 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 60 118 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 60 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 118 2 1 30 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 118
  (Polychromatic418967fa.accept_19_1_3_4_1_4306 1 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 118))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 118 (allA_of_3_1 59 59 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 118 (allA_succ_of_accept 57 58 118
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 118 2 28 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 58 118 (Polychromatic418967fa.accept_13_3_6_1_1_3797 55 58 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 118 2 27 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 118 (accept_3_3 53 58 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 118 2 26 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 118 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 58 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 118 2 25 29 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 118
  (Polychromatic418967fa.accept_11_5_3_8_1_454 49 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 118 2 24 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 58 118 (accept_3_3 47 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58
  118 2 23 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  58 118 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 58 118 2 22 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 58 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 58 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 118 2 21 29 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 118 (accept_3_3 41 58 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 118 2 20 29 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 118
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 58 118 2 19 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 58 118 (Polychromatic418967fa.accept_17_3_7_16_1_3251 37 58 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 118 2 18 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 118 (accept_3_3 35 58 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 118 2 17 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 118 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 58 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 118 2 16 29 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 118
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 118 2 15 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 58 118 (accept_3_3 29 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58
  118 2 14 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  58 118 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 58 118 2 13 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 58 118 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 58 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 118 2 12 29 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 118 (accept_3_3 23 58 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 118 2 11 29 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 118
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 118 2 10 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 118 (Polychromatic418967fa.accept_21_19_16_13_1_4099 19 58 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 118 2 9 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 118 (accept_3_3 17 58 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 118 2 8 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 58 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 118 2 7 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 118 (Polychromatic418967fa.accept_18_13_4_10_1_1076
  13 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 118 2 6 29 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 118 (accept_3_3 11
  58 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 118 2 5 29 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 118
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 118 2 4 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 118 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 58 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 118 2 3 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 118 (accept_3_3 5 58 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 118 2 2 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 118 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 58 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 118 2 1 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 58
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  118)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 118 (allA_succ_of_accept 56 57 118
  (accept_3_3 56 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 118
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 118 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 118 (accept_3_3 53 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 118 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 118 (accept_3_3 50 57
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 118 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 118
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 48 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 118 (accept_3_3 47 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 118 (Polychromatic418967fa.accept_15_1_12_13_1_944 46 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 118 (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 118 (accept_3_3 44 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 118
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 118 (accept_3_3 41 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 118 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 118 (accept_3_3 38 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 118
  (Polychromatic418967fa.accept_25_11_7_18_1_2221 36 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 118 (accept_3_3 35 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 118 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 118 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 118 (accept_3_3 32 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 118
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 118 (accept_3_3 29 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 118 (Polychromatic418967fa.accept_21_7_15_13_1_5606 28 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 118 (accept_3_3 26 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 118
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 118 (accept_3_3 23 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 118 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 118 (Polychromatic418967fa.accept_13_8_5_1_1_1381 21 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 118 (accept_3_3 20 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 118
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 118 (accept_3_3 17 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 118 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 118 (accept_3_3 14 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 118
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 118 (accept_3_3 11 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 118 (Polychromatic418967fa.accept_15_10_12_13_1_2585 10 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 118 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 118 (accept_3_3 8 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 118
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 118 (accept_3_3 5 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  118 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 118 (accept_3_3 2 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 118)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 118 (allA_of_3_1 56 56 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 118
  (allA_succ_of_accept 54 55 118 (Polychromatic418967fa.accept_13_2_3_1_1_3823 54 55 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 118 (accept_3_3 53 55 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 118 (Polychromatic418967fa.accept_10_2_5_8_1_139 52 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 51
  55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 118 (accept_3_3 50 55
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 118 (Polychromatic418967fa.accept_4_1_3_2_1_3
  49 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 118
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 48 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 118 (accept_3_3 47 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 118 (Polychromatic418967fa.accept_13_7_3_1_1_814 46 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 118 (accept_3_3 44 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 118 (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 55 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 118
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 118 (accept_3_3 41 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 118 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 118 (accept_3_3 38 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 118
  (Polychromatic418967fa.accept_20_16_15_18_1_5605 36 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 55 118 (accept_3_3 35 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 55 118 (Polychromatic418967fa.accept_15_4_10_13_1_2565 34 55 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 55 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 118 (accept_3_3 32 55 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 118 (Polychromatic418967fa.accept_13_5_3_1_1_1398
  31 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 118
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 30 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 118 (accept_3_3 29 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 118 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 118 (accept_3_3 26 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 55 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 118
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 118 (accept_3_3 23 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 118 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 118 (accept_3_3 20 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 118 (Polychromatic418967fa.accept_13_6_3_1_1_1413 19 55 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 118
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 118 (accept_3_3 17 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 118 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 118 (accept_3_3 14 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 118
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 118 (accept_3_3 11 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 118 (Polychromatic418967fa.accept_19_10_17_4_1_4227 10 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 118 (accept_3_3 8 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 118 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 55 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 118
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 6 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 118 (accept_3_3 5 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  118 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 55 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 118 (accept_3_3 2 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  118))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 118 (allA_succ_of_accept 53 54 118
  (accept_3_3 53 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 118 2 26 27 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 118
  (Polychromatic418967fa.accept_12_3_6_10_1_576 51 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 54 118 2 25 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 54 118 (Polychromatic418967fa.accept_10_9_4_8_1_741 49 54 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 118 2 24 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 118 (accept_3_3 47 54 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 118 2 23 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 118 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 54 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 118 2 22 27 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 118
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 118 2 21 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 118 (accept_3_3 41 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54
  118 2 20 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  54 118 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 54 118 2 19 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 54 118 (Polychromatic418967fa.accept_15_7_9_13_1_3451 37 54 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 118 2 18 27 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 118 (accept_3_3 35 54 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 118 2 17 27 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 118
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 118 2 16 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 54 118 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 54 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 118 2 15 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 118 (accept_3_3 29 54 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 118 2 14 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 118 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 54 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 118 2 13 27 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 118
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 118 2 12 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 118 (accept_3_3 23 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54
  118 2 11 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  54 118 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 54 118 2 10 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 54 118 (Polychromatic418967fa.accept_10_9_4_8_1_741 19 54 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 118 2 9 27 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 118 (accept_3_3 17 54 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 118 2 8 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 118 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 54 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 118 2 7 27 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 118
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 118 2 6 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 118 (accept_3_3 11 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54
  118 2 5 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  54 118 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 54 118 2 4 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 54 118 (Polychromatic418967fa.accept_15_7_9_13_1_3451 7 54 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 118 2 3 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 118 (accept_3_3 5 54 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 118 2 2 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 54 118 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 54 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 118 2 1 27 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 118
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 118)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 118 (allA_of_3_1 53 53 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 118 (allA_succ_of_accept 51 52 118
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 52 118 2 25 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 52 118 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 52 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 118 2 24 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 118 (accept_3_3 47 52 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 118 2 23 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 118 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 52 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 118 2 22 26 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 118
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 118 2 21 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 52 118 (accept_3_3 41 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52
  118 2 20 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  52 118 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 52 118 2 19 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 52 118 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 52 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 118 2 18 26 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 118 (accept_3_3 35 52 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 118 2 17 26 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 118
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 52 118 2 16 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 52 118 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 52 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 118 2 15 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 118 (accept_3_3 29 52 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 118 2 14 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 118 (Polychromatic418967fa.accept_16_11_4_6_1_4422 27 52 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 118 2 13 26 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 118
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 52 118 2 12 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 52 118 (accept_3_3 23 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52
  118 2 11 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  52 118 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 52 118 2 10 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 52 118 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 52 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 118 2 9 26 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 118 (accept_3_3 17 52 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 118 2 8 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 52 118 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 52 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 118 2 7 26 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 118
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 52 118 2 6 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 52 118 (accept_3_3 11 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52
  118 2 5 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  52 118 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 52 118 2 4 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 52 118 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 52 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 118 2 3 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 118 (accept_3_3 5 52 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 52 118 2 2 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 52 118 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 52 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 118 2 1 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 118 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  118)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 118 (allA_succ_of_accept 50 51 118 (accept_3_3
  50 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 118
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 118 (accept_3_3 47 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 118 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 51 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 118 (accept_3_3 44 51
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 118 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 51 118
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 51 118 (accept_3_3 41 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  51 118 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 51 118 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 51 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 118 (accept_3_3 38 51 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 118
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 118 (accept_3_3 35 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  51 118 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 118 (accept_3_3 32 51 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 118
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 118 (accept_3_3 29 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 118 (Polychromatic418967fa.accept_13_2_12_1_1_343 28 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 118 (Polychromatic418967fa.accept_16_11_3_6_1_4462 27 51 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 118 (accept_3_3 26 51 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 118
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 118 (accept_3_3 23 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 118 (accept_3_3 20 51 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 118
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 118 (accept_3_3 17 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 118 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 51 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 118 (accept_3_3 14 51 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 118
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 118 (accept_3_3 11 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 118 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 118 (accept_3_3 8 51 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 118
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 118 (accept_3_3 5 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  118 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 118 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 118 (accept_3_3 2 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 118)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 118 (allA_of_3_1 50 50 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 118
  (allA_succ_of_accept 48 49 118 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 118 (accept_3_3 47 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 118 (Polychromatic418967fa.accept_11_2_5_8_1_470 46 49 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 45
  49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 118 (accept_3_3 44 49
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 118 (Polychromatic418967fa.accept_4_3_1_2_1_62
  43 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 118
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 118 (accept_3_3 41 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 118 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 118 (accept_3_3 38 49 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 118 (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 49 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 118
  (Polychromatic418967fa.accept_11_3_5_8_1_458 36 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 118 (accept_3_3 35 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 118 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 118 (accept_3_3 32 49 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 118
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 118 (accept_3_3 29 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 118 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 118 (accept_3_3 26 49 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 118 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 49 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 118
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 118 (accept_3_3 23 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 118 (Polychromatic418967fa.accept_13_9_10_1_1_1389 22 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 118 (accept_3_3 20 49 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 118
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 18 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 118 (accept_3_3 17 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 118 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 118 (accept_3_3 14 49 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 118 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 49 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 118
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 118 (accept_3_3 11 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 118 (Polychromatic418967fa.accept_15_10_4_13_1_4506 10 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 118 (accept_3_3 8 49 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 118
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 118 (accept_3_3 5 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  118 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 118 (accept_3_3 2 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 118 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 49 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 118))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 118 (allA_succ_of_accept 47 48 118 (accept_3_3 47 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  46 48 118 2 23 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 48 118 (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 48 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 118 2 22 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 118 (Polychromatic418967fa.accept_9_7_3_1_1_386 43
  48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 118 2 21 24 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 118 (accept_3_3 41
  48 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 118 2 20 24 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 118
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 48 118 2 19 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 48 118 (Polychromatic418967fa.accept_13_11_9_1_1_1407 37 48 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 118 2 18 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 118 (accept_3_3 35 48 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 118 2 17 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 118 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 48 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 118 2 16 24 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 118
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 118 2 15 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 118 (accept_3_3 29 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48
  118 2 14 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  48 118 (Polychromatic418967fa.accept_15_12_3_13_1_4481 27 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 48 118 2 13 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 48 118 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 48 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 118 2 12 24 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 118 (accept_3_3 23 48 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 118 2 11 24 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 118
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 118 2 10 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 118 (Polychromatic418967fa.accept_13_6_9_1_1_5604 19 48 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 118 2 9 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 118 (accept_3_3 17 48 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 118 2 8 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 118 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 48 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 118 2 7 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 118 (Polychromatic418967fa.accept_9_4_3_1_1_154 13
  48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 118 2 6 24 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 118 (accept_3_3 11
  48 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 118 2 5 24 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 118
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 118 2 4 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 118 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 48 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 118 2 3 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 118 (accept_3_3 5 48 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 48 118 2 2 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 48 118 (Polychromatic418967fa.accept_20_3_8_18_1_5603 3 48 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 118 2 1 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 118 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1
  48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  118)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 118 (allA_of_3_1 47 47 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 46 118 (allA_succ_of_accept 45 46 118 (Polychromatic418967fa.accept_7_3_4_6_1_329 45
  46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 46 118 2 22 23 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 46 118
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 46 118 2 21 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 46 118 (accept_3_3 41 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46
  118 2 20 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  46 118 (Polychromatic418967fa.accept_21_18_4_13_1_5602 39 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 46 118 2 19 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 46 118 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 46 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 118 2 18 23 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 118 (accept_3_3 35 46 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 118 2 17 23 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 118
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 46 118 2 16 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 46 118 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 46 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 118 2 15 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 118 (accept_3_3 29 46 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 118 2 14 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 118 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 46 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 118 2 13 23 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 118
  (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 46 118 2 12 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 46 118 (accept_3_3 23 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46
  118 2 11 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  46 118 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 46 118 2 10 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 46 118 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 46 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 118 2 9 23 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 118 (accept_3_3 17 46 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46 118 2 8 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 46 118 (Polychromatic418967fa.accept_19_15_8_4_1_2962 15 46 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 118 2 7 23 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 118
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 46 118 2 6 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 46 118 (accept_3_3 11 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46
  118 2 5 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  46 118 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 46 118 2 4 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 46 118 (Polychromatic418967fa.accept_21_7_4_13_1_4125 7 46 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 118 2 3 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 118 (accept_3_3 5 46 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 118 2 2 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 46 118 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 46 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 118 2 1 23 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 118
  (Polychromatic418967fa.accept_17_1_12_16_1_2211 1 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 46 118)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 118 (allA_succ_of_accept 44 45 118
  (accept_3_3 44 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 118
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 118 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 45 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 118 (accept_3_3 41 45 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 118 (Polychromatic418967fa.accept_19_2_7_4_1_5601 40 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 118 (accept_3_3 38 45
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 118 (Polychromatic418967fa.accept_6_1_3_4_1_1
  37 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 118
  (Polychromatic418967fa.accept_16_4_13_6_1_4417 36 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 118 (accept_3_3 35 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 118 (Polychromatic418967fa.accept_13_8_6_1_1_3808 34 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 118 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 118 (accept_3_3 32 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 118
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 118 (accept_3_3 29 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 118 (Polychromatic418967fa.accept_13_2_6_1_1_3807 28 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 118 (accept_3_3 26 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 118
  (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 118 (accept_3_3 23 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 118 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 118 (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 118 (accept_3_3 20 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 118
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 118 (accept_3_3 17 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 118 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 118 (accept_3_3 14 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 118
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 118 (accept_3_3 11 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 118 (Polychromatic418967fa.accept_14_10_3_6_1_2728 10 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 118 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 118 (accept_3_3 8 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 118
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 118 (accept_3_3 5 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  118 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 118 (accept_3_3 2 45 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 118))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  118 (allA_of_3_1 44 44 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 118 (allA_succ_of_accept 42 43 118
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 118 (accept_3_3 41 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 118 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 118 (accept_3_3 38 43 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 118
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 118 (accept_3_3 35 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 118 (Polychromatic418967fa.accept_16_2_11_6_1_737 34 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 118 (accept_3_3 32 43 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 118 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 43 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 118
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 118 (accept_3_3 29 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 118 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 118 (accept_3_3 26 43 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 118
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 118 (accept_3_3 23 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 118 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 118 (accept_3_3 20 43 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 118 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 43 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 118
  (Polychromatic418967fa.accept_13_5_4_1_1_364 18 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 118 (accept_3_3 17 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 118 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 118 (accept_3_3 14 43 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 118
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 118 (accept_3_3 11 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 118 (Polychromatic418967fa.accept_13_10_4_1_1_2142 10 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 118 (accept_3_3 8 43 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 118 (Polychromatic418967fa.accept_14_7_1_6_1_3514 7 43 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 118
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 118 (accept_3_3 5 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  118 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 118 (accept_3_3 2 43 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 118))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 118
  (allA_succ_of_accept 41 42 118 (accept_3_3 41 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42
  118 2 20 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  42 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 42 118 2 19 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 42 118 (Polychromatic418967fa.accept_13_11_3_1_1_1397 37 42 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 118 2 18 21 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 118 (accept_3_3 35 42 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 118 2 17 21 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 118
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 118 2 16 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 118 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 42 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 118 2 15 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 118 (accept_3_3 29 42 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 118 2 14 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 118 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 42 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 118 2 13 21 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 118
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 118 2 12 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 118 (accept_3_3 23 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42
  118 2 11 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  42 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 42 118 2 10 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 42 118 (Polychromatic418967fa.accept_13_6_3_1_1_1413 19 42 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 118 2 9 21 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 118 (accept_3_3 17 42 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 118 2 8 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 118 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 42 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 118 2 7 21 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 118
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 42 118 2 6 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 42 118 (accept_3_3 11 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42
  118 2 5 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  42 118 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 42 118 2 4 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 42 118 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 42 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 118 2 3 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 118 (accept_3_3 5 42 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 118 2 2 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 42 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 42 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 118 2 1 21 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 118
  (Polychromatic418967fa.accept_15_1_12_13_1_944 1 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 118)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 118 (allA_of_3_1 41 41 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 40 118 (allA_succ_of_accept 39 40 118
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 118 2 19 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 118 (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 40 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 118 2 18 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 118 (accept_3_3 35 40 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 118 2 17 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 118 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 40 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 118 2 16 20 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 118
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 118 2 15 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 118 (accept_3_3 29 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  118 2 14 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 118 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 118 2 13 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 40 118 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 40 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 118 2 12 20 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 118 (accept_3_3 23 40 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 118 2 11 20 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 118
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 118 2 10 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 118 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 40 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 118 2 9 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 118 (accept_3_3 17 40 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 40 118 2 8 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 40 118 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 40 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 118 2 7 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 118 (Polychromatic418967fa.accept_12_1_4_10_1_209
  13 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 118 2 6 20 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 118 (accept_3_3 11
  40 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 118 2 5 20 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 118
  (Polychromatic418967fa.accept_17_9_6_16_1_3280 9 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 118 2 4 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 118 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 40 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 118 2 3 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 118 (accept_3_3 5 40 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 40 118 2 2 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 40 118 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 40 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 118 2 1 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 118 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 40
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  118)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 118 (allA_succ_of_accept 38 39 118 (accept_3_3 38 39 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 118
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 118 (accept_3_3 35 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  39 118 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 118 (accept_3_3 32 39 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 118
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 118 (accept_3_3 29 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 118 (Polychromatic418967fa.accept_17_11_5_16_1_5600 28 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 118 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 39 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 118 (accept_3_3 26 39 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 118
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 118 (accept_3_3 23 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 118 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 118 (accept_3_3 20 39 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 118
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 118 (accept_3_3 17 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 118 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 118 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 39 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 118 (accept_3_3 14 39 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 118
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 118 (accept_3_3 11 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 118 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 118 (accept_3_3 8 39 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 118
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 118 (accept_3_3 5 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  118 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 118 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 39 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 118 (accept_3_3 2 39 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 118))))))))))))))))))))))))))))))))))))))) (allB_succ 38 118
  (allA_of_3_1 38 38 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 118 (allA_succ_of_accept 36 37 118
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 118 (accept_3_3 35 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 118 (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 118 (accept_3_3 32 37 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 118
  (Polychromatic418967fa.accept_17_13_3_16_1_5599 30 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 118 (accept_3_3 29 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 118 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 118 (accept_3_3 26 37 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 118 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 37 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 118
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 118 (accept_3_3 23 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 118 (accept_3_3 20 37 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 118
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 118 (accept_3_3 17 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 118 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 118 (accept_3_3 14 37 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 118 (Polychromatic418967fa.accept_17_13_3_16_1_5599 13 37 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 118
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 118 (accept_3_3 11 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 118 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 118 (accept_3_3 8 37 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 118
  (Polychromatic418967fa.accept_15_6_7_13_1_1666 6 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 118 (accept_3_3 5 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  118 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 118 (accept_3_3 2 37 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 37 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 118))))))))))))))))))))))))))))))))))))) (allB_succ 36 118
  (allA_succ_of_accept 35 36 118 (accept_3_3 35 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36
  118 2 17 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  36 118 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 36 118 2 16 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 36 118 (Polychromatic418967fa.accept_17_14_2_16_1_4380 31 36 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 118 2 15 18 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 118 (accept_3_3 29 36 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 118 2 14 18 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 118
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 118 2 13 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 118 (Polychromatic418967fa.accept_17_8_2_16_1_5598 25 36 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 118 2 12 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 118 (accept_3_3 23 36 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 118 2 11 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 118 (Polychromatic418967fa.accept_14_7_8_6_1_1164 21 36 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 118 2 10 18 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 118
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 118 2 9 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 118 (accept_3_3 17 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36
  118 2 8 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  36 118 (Polychromatic418967fa.accept_20_15_16_18_1_5597 15 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 36 118 2 7 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 36 118 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 36 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 118 2 6 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 118 (accept_3_3 11 36 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 118 2 5 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 36 118 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 36 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 118 2 4 18 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 118
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 118 2 3 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 118 (accept_3_3 5 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 118
  2 2 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36
  118 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 36 118 2 1 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 36 118 (Polychromatic418967fa.accept_17_1_2_16_1_5596 1 36 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 118)))))))))))))))))))))))))))))))))))) (allB_succ 35 118
  (allA_of_3_1 35 35 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 118 (allA_succ_of_accept 33 34 118
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 34 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 118 2 16 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 118 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 34 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 118 2 15 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 118 (accept_3_3 29 34 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 118 2 14 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 118 (Polychromatic418967fa.accept_16_11_2_6_1_1435 27 34 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 118 2 13 17 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 118
  (Polychromatic418967fa.accept_13_12_8_1_1_825 25 34 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 118 2 12 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 118 (accept_3_3 23 34 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  118 2 11 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 118 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 34 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 118 2 10 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 118 (Polychromatic418967fa.accept_10_9_4_8_1_741 19 34 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 118 2 9 17 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 118 (accept_3_3 17 34 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34 118 2 8 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 118 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 34 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 118 2 7 17 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 118
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 34 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 118 2 6 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 118 (accept_3_3 11 34 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  118 2 5 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 118 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 34 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 118 2 4 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 118 (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 34 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 118 2 3 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 118 (accept_3_3 5 34 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 118 2 2 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 118 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 34 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 118 2 1 17 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 118
  (Polychromatic418967fa.accept_16_1_2_6_1_2295 1 34 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 118)))))))))))))))))))))))))))))))))) (allB_succ 33 118 (allA_succ_of_accept 32 33 118 (accept_3_3 32 33
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 118 (Polychromatic418967fa.accept_4_3_1_2_1_62
  31 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 118
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 118 (accept_3_3 29 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  33 118 (Polychromatic418967fa.accept_19_9_14_4_1_5595 28 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 118 (accept_3_3 26 33 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 118
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 33 118 (accept_3_3 23 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  33 118 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 33 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 33 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 118 (accept_3_3 20 33 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 118
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 118 (accept_3_3 17 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 118 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 118 (accept_3_3 14 33 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 118
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 118 (accept_3_3 11 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  33 118 (Polychromatic418967fa.accept_15_10_3_13_1_4480 10 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 118 (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 33 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 118 (accept_3_3 8 33 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 118
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 118 (accept_3_3 5 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  118 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 118 (accept_3_3 2 33 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 118))))))))))))))))))))))))))))))))) (allB_succ 32 118
  (allA_of_3_1 32 32 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 118 (allA_succ_of_accept 30 31 118
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 118 (accept_3_3 29 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 118 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 31 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 118 (accept_3_3 26 31 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 118
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 118 (accept_3_3 23 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 118 (Polychromatic418967fa.accept_13_9_5_1_1_1382 22 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 118 (accept_3_3 20 31 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 118 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 31 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 118
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 118 (accept_3_3 17 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 118 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 118 (accept_3_3 14 31 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 118
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 118 (accept_3_3 11 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 118 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 118 (accept_3_3 8 31 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 118 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 31 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 118
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 118 (accept_3_3 5 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  118 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 118 (accept_3_3 2 31 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 118))))))))))))))))))))))))))))))) (allB_succ 30 118
  (allA_succ_of_accept 29 30 118 (accept_3_3 29 30 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  118 2 14 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  30 118 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 30 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 118 2 13 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 30 118 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 30 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 118 2 12 15 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 118 (accept_3_3 23 30 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 118 2 11 15 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 118
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 30 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 118 2 10 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 118 (Polychromatic418967fa.accept_23_19_7_3_1_5594 19 30 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 118 2 9 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 118 (accept_3_3 17 30 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 118 2 8 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 30 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 118 2 7 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 118 (Polychromatic418967fa.accept_9_4_3_1_1_154 13
  30 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 118 2 6 15 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 118 (accept_3_3 11
  30 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 118 2 5 15 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 118
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 30 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 118 2 4 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 118 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 30 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 118 2 3 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 118 (accept_3_3 5 30 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 30 118 2 2 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 118 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 30 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 118 2 1 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 30
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 118))))))))))))))))))))))))))))))
  (allB_succ 29 118 (allA_of_3_1 29 29 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 118
  (allA_succ_of_accept 27 28 118 (Polychromatic418967fa.accept_19_8_9_4_1_5593 27 28 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 118 2 13 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 118 (Polychromatic418967fa.accept_11_3_6_8_1_1924
  25 28 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 118 2 12 14 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 118 (accept_3_3 23
  28 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 118 2 11 14 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 118
  (Polychromatic418967fa.accept_19_2_9_4_1_2951 21 28 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 28 118 2 10 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 28 118 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 28 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 118 2 9 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 118 (accept_3_3 17 28 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 28 118 2 8 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 28 118 (Polychromatic418967fa.accept_17_15_11_16_1_3263 15 28 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 118 2 7 14 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 118
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 28 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 28 118 2 6 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 28 118 (accept_3_3 11 28 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28
  118 2 5 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  28 118 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 28 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 28 118 2 4 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 28 118 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 28 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 118 2 3 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 118 (accept_3_3 5 28 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 118 2 2 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 28 118 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 28 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 118 2 1 14 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 118
  (Polychromatic418967fa.accept_12_1_4_10_1_209 1 28 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 118)))))))))))))))))))))))))))) (allB_succ 27 118 (allA_succ_of_accept 26 27 118 (accept_3_3 26 27 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 118
  (Polychromatic418967fa.accept_11_2_5_8_1_470 24 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 118 (accept_3_3 23 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  27 118 (Polychromatic418967fa.accept_19_3_8_4_1_5592 22 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 118 (accept_3_3 20 27 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 118
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 118 (accept_3_3 17 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  27 118 (Polychromatic418967fa.accept_15_1_12_13_1_944 16 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 118 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 27 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 118 (accept_3_3 14 27 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 118
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 118 (accept_3_3 11 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  27 118 (Polychromatic418967fa.accept_15_10_12_13_1_2585 10 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 118 (accept_3_3 8 27 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 118
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 118 (accept_3_3 5 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27
  118 (Polychromatic418967fa.accept_16_4_11_6_1_5591 4 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 118 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 27 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 118 (accept_3_3 2 27 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 118))))))))))))))))))))))))))) (allB_succ 26 118
  (allA_of_3_1 26 26 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 118 (allA_succ_of_accept 24 25 118
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 118 (accept_3_3 23 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 118 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 25 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 118 (accept_3_3 20 25 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 25 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 118
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 118 (accept_3_3 17 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 118 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 25 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 118 (accept_3_3 14 25 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 118 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 25 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 118
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 118 (accept_3_3 11 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 118 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 118 (accept_3_3 8 25 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 118
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 118 (accept_3_3 5 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  118 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 118 (accept_3_3 2 25 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 118 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 25 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 118))))))))))))))))))))))))) (allB_succ 24 118
  (allA_succ_of_accept 23 24 118 (accept_3_3 23 24 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24
  118 2 11 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  24 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 24 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 24 118 2 10 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 24 118 (Polychromatic418967fa.accept_10_9_4_8_1_741 19 24 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 118 2 9 12 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 118 (accept_3_3 17 24 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 118 2 8 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 118 (Polychromatic418967fa.accept_18_15_6_10_1_5590 15 24
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 118 2 7 12 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 118
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 24 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 118 2 6 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 118 (accept_3_3 11 24 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24
  118 2 5 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  24 118 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 24 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 118 2 4 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 118 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 24 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 118 2 3 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 118 (accept_3_3 5 24 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 24 118 2 2 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 24 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 24 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 118 2 1 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 118 (Polychromatic418967fa.accept_19_1_5_4_1_4246 1
  24 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 118))))))))))))))))))))))))
  (allB_succ 23 118 (allA_of_3_1 23 23 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 118
  (allA_succ_of_accept 21 22 118 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 22 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 22 118 2 10 11 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 22 118 (Polychromatic418967fa.accept_7_5_1_6_1_163 19
  22 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 118 2 9 11 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 118 (accept_3_3 17
  22 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22 118 2 8 11 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 22 118
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 22 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 22 118 2 7 11 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 22 118 (Polychromatic418967fa.accept_18_13_4_10_1_1076 13 22 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 118 2 6 11 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 118 (accept_3_3 11 22 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 22 118 2 5 11 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 22 118 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 22 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 22 118 2 4 11 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 22 118 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 22
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 118 2 3 11 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 118 (accept_3_3 5 22
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 118 2 2 11 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 22 118
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 22 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 22 118 2 1 11 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 22 118 (Polychromatic418967fa.accept_17_1_5_16_1_5589 1 22 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 22 118)))))))))))))))))))))) (allB_succ 21 118 (allA_succ_of_accept 20 21
  118 (accept_3_3 20 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 118
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 21 118 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 21 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 118 (accept_3_3 17 21 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 21 118 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 21 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 118 (accept_3_3 14 21
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 118 (Polychromatic418967fa.accept_6_1_3_4_1_1
  13 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 118
  (Polychromatic418967fa.accept_13_12_8_1_1_825 12 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 118 (accept_3_3 11 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  21 118 (Polychromatic418967fa.accept_29_10_21_2_1_5588 10 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 118 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 21 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 118 (accept_3_3 8 21 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 118
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 118 (accept_3_3 5 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  118 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 118 (accept_3_3 2 21 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 118))))))))))))))))))))) (allB_succ 20 118 (allA_of_3_1 20 20
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 118 (allA_succ_of_accept 18 19 118
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 118 (accept_3_3 17 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 118 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 118 (accept_3_3 14 19 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 118
  (Polychromatic418967fa.accept_23_12_19_3_1_5587 12 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 118 (accept_3_3 11 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 118 (Polychromatic418967fa.accept_15_10_4_13_1_4506 10 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 118 (accept_3_3 8 19 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 118 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 19 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 118
  (Polychromatic418967fa.accept_15_6_4_13_1_403 6 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 118 (accept_3_3 5 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  118 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 118 (accept_3_3 2 19 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 118))))))))))))))))))) (allB_succ 18 118 (allA_succ_of_accept 17
  18 118 (accept_3_3 17 18 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 118 2 8 9 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 118
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 18 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 118 2 7 9 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 118 (Polychromatic418967fa.accept_29_13_18_2_1_5586 13 18 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 118 2 6 9 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 118 (accept_3_3 11 18 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 118 2 5 9 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 118 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 18 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 118 2 4 9 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 118 (Polychromatic418967fa.accept_21_7_18_13_1_5585
  7 18 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 118 2 3 9 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 118 (accept_3_3 5 18
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 118 2 2 9 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 118
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 18 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 118 2 1 9 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 118 (Polychromatic418967fa.accept_15_1_3_13_1_2548 1 18 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 118)))))))))))))))))) (allB_succ 17 118 (allA_of_3_1 17 17 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 118 (allA_succ_of_accept 15 16 118
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 16 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 118 2 7 8 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 118 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 16 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 118 2 6 8 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 118 (accept_3_3 11 16 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 118 2 5 8 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 118 (Polychromatic418967fa.accept_19_9_16_4_1_5584 9 16 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 118 2 4 8 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 118 (Polychromatic418967fa.accept_12_7_4_10_1_572 7
  16 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 118 2 3 8 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 118 (accept_3_3 5 16
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 118 2 2 8 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 118
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 16 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 118 2 1 8 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 118 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 16 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 118)))))))))))))))) (allB_succ 15 118 (allA_succ_of_accept 14 15 118
  (accept_3_3 14 15 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 118
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 118 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 15 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 118 (accept_3_3 11 15 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 118 (Polychromatic418967fa.accept_19_10_15_4_1_1852 10 15 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 118
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 118 (accept_3_3 8 15 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15
  118 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 15 118 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 15 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 118 (accept_3_3 5 15 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 15 118 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 15 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 118 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 15
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 118 (accept_3_3 2 15 118
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15
  118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 118))))))))))))))) (allB_succ 14 118
  (allA_of_3_1 14 14 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 118 (allA_succ_of_accept 12 13 118
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 13 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 118 (accept_3_3 11 13 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 118 (Polychromatic418967fa.accept_19_10_13_4_1_5583 10 13 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 118 (accept_3_3 8 13 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 118
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 13 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 118 (accept_3_3 5 13 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  118 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 13 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 118 (accept_3_3 2 13 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 118 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 13 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 118))))))))))))) (allB_succ 12 118
  (allA_succ_of_accept 11 12 118 (accept_3_3 11 12 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12
  118 2 5 6 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12
  118 (Polychromatic418967fa.accept_18_9_12_10_1_387 9 12 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 12 118 2 4 6 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 12 118 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 12 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 118 2 3 6 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 118 (accept_3_3 5 12 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 118 2 2 6 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 12 118 (Polychromatic418967fa.accept_15_3_12_13_1_2549 3 12 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 118 2 1 6 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 118
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 12 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 118)))))))))))) (allB_succ 11 118 (allA_of_3_1 11 11 118 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 118 (allA_succ_of_accept 9 10 118 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 10 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 118 2 4 5 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 118 (Polychromatic418967fa.accept_17_7_10_16_1_5582
  7 10 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 118 2 3 5 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 118 (accept_3_3 5 10
  118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 118 2 2 5 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 118
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 3 10 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 10 118 2 1 5 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 10 118 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 10 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 10 118)))))))))) (allB_succ 9 118 (allA_succ_of_accept 8 9 118 (accept_3_3 8
  9 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 118 (Polychromatic418967fa.accept_4_3_1_2_1_62
  7 9 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 118
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 9 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 118 (accept_3_3 5 9 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 118
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 9 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 118 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 118 (accept_3_3 2 9 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 118 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 118))))))))) (allB_succ 8 118 (allA_of_3_1 8 8 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 118 (allA_succ_of_accept 6 7 118
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 7 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 118 (accept_3_3 5 7 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 118
  (Polychromatic418967fa.accept_9_4_7_1_1_379 4 7 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 118 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 118 (accept_3_3 2 7 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 118))))))) (allB_succ 6 118 (allA_succ_of_accept 5 6 118
  (accept_3_3 5 6 118 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 118 2 2 3 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 118
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 6 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 118 2 1 3 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 118 (Polychromatic418967fa.accept_23_1_6_3_1_5581 1 6 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 118)))))) (allB_succ 5 118 (allA_of_3_1 5 5 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 118 (allA_succ_of_accept 3 4 118 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 4 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 118 2 1 2 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 118
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 4 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 118)))) (allB_succ 3 118 (allA_succ_of_accept 2 3 118 (accept_3_3 2 3 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 118 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 118))) (allB_succ 2 118 (allA_of_3_1 2 2 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  118))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


