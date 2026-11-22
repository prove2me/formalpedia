-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch170
-- name    : Polychromatic418967fa_Branch170
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:18:42.97159+00:00
-- url     : https://prove2.me/theorems/1a9b993c-c45f-491b-94bc-9b59e56522a4
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

def Polychromatic418967fa.branch_170 : allB 170 170 :=
  allB_succ' 2 169 170 (Eq.refl Bool.true) (allA_of_3_0 2 169 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  168 170 (Eq.refl Bool.true) (allA_succ_of_gcd 2 168 170 2 1 84 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 170 (accept_3_2 1 168 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 168 170))) (allB_succ' 4 167 170 (Eq.refl Bool.true) (allA_succ_of_accept 3 167 170
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 167 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 167 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 167 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 170 (accept_3_2 1 167 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 167 170)))) (allB_succ' 5 166 170 (Eq.refl Bool.true) (allA_of_3_0 5 166 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 165 170 (Eq.refl Bool.true) (allA_succ_of_gcd 5 165 170 5 1 33 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 165 170 (accept_3_2 4
  165 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 165 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 165 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 165 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 170 (accept_3_2 1 165 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 165 170)))))) (allB_succ' 7 164 170 (Eq.refl Bool.true) (allA_succ_of_gcd 6 164 170 2 3 82 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 164 170
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 164 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 164 170 2 2 82 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 164 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 164 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 170 2 1 82 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 170 (accept_3_2 1 164 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 164 170))))))) (allB_succ' 8 163 170 (Eq.refl Bool.true) (allA_of_3_0 8 163 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 162 170 (Eq.refl Bool.true) (allA_succ_of_gcd 8 162 170 2 4 81 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 170
  (accept_3_2 7 162 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 170 2 3 81 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 170
  (Polychromatic418967fa.accept_13_5_6_1_1_822 5 162 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 162 170 2 2 81 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 162 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 162 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 170 2 1 81 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 170 (accept_3_2 1 162 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 162 170))))))))) (allB_succ' 10 161 170 (Eq.refl Bool.true) (allA_succ_of_accept 9 161 170
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 161 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 161 170 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 161 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 170 (accept_3_2 7 161 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 161 170 (Polychromatic418967fa.accept_13_6_5_1_1_834 6 161 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 170 (Polychromatic418967fa.accept_14_5_7_2_1_468 5
  161 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 170 (accept_3_2 4 161
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 170 (Polychromatic418967fa.accept_4_3_1_2_1_62
  3 161 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 170
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 2 161 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 170 (accept_3_2 1 161 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  170)))))))))) (allB_succ' 11 160 170 (Eq.refl Bool.true) (allA_of_3_0 11 160 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 159 170 (Eq.refl Bool.true) (allA_succ_of_accept 11 159 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 159 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 170 (accept_3_2 10 159 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  159 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 159 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 159 170 (Polychromatic418967fa.accept_19_8_7_18_1_1595 8 159 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 170 (accept_3_2 7 159 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 159 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 159 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 170 (accept_3_2 4 159 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 159 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 159 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 170 (accept_3_2 1 159 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159 170)))))))))))) (allB_succ' 13 158 170 (Eq.refl Bool.true) (allA_succ_of_gcd 12 158
  170 2 6 79 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  158 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 158 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 158 170 2 5 79 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 158 170 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 158 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 158 170 2 4 79 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 158 170 (accept_3_2 7 158 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158 170 2 3 79 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 158 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 158 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 158 170 2 2 79 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 158 170
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 158 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 158 170 2 1 79 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 158 170 (accept_3_2 1 158 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  170))))))))))))) (allB_succ' 14 157 170 (Eq.refl Bool.true) (allA_of_3_0 14 157 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 156 170 (Eq.refl Bool.true) (allA_succ_of_gcd 14 156 170 2 7 78 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 170 (accept_3_2 13 156 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 170 2 6 78 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 156 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 170 2 5 78 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 156 170 (Polychromatic418967fa.accept_20_9_16_10_1_3559 9 156 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 156 170 2 4 78 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 170 (accept_3_2 7 156 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 156 170 2 3 78 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 156 170 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 156 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 170 2 2 78 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 156 170 (Polychromatic418967fa.accept_15_3_6_5_1_2079 3
  156 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 170 2 1 78 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 170 (accept_3_2 1
  156 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 170))))))))))))))) (allB_succ' 16 155 170 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 155 170 5 3 31 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 155 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 155 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 170 (accept_3_2 13 155 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 155 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 170
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 155 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 155 170 5 2 31 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 155 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 155 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 170
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 155 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 170 (accept_3_2 7 155 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 155 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 155 170 5 1 31 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 155 170 (accept_3_2 4 155 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 155 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 170 (Polychromatic418967fa.accept_13_2_12_1_1_343 2 155 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 170 (accept_3_2 1 155 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155 170)))))))))))))))) (allB_succ' 17 154 170 (Eq.refl Bool.true)
  (allA_of_3_0 17 154 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 153 170 (Eq.refl Bool.true)
  (allA_succ_of_gcd 17 153 170 17 1 9 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 16 153 170 (accept_3_2 16 153 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 153 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 153 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 153 170 (Polychromatic418967fa.accept_19_14_1_18_1_5280 14 153 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 170 (accept_3_2 13 153 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 170 (Polychromatic418967fa.accept_19_12_1_18_1_9570 12 153
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 153 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 170 (accept_3_2 10 153 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  153 170 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 153 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 153 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 153 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 170 (accept_3_2 7 153 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 170 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 153 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 170 (accept_3_2 4 153 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 153 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 170 (Polychromatic418967fa.accept_15_2_3_5_1_2991 2 153 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 170 (accept_3_2 1 153 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 153 170)))))))))))))))))) (allB_succ' 19 152 170 (Eq.refl Bool.true) (allA_succ_of_gcd
  18 152 170 2 9 76 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 152 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 152 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 170 2 8 76 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 170 (Polychromatic418967fa.accept_13_2_9_1_1_67 15
  152 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 170 2 7 76 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 170 (accept_3_2 13
  152 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 170 2 6 76 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 170
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 152 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 152 170 2 5 76 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 152 170 (Polychromatic418967fa.accept_25_9_2_20_1_3970 9 152 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 170 2 4 76 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 170 (accept_3_2 7 152 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 152 170 2 3 76 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 152 170 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 152 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 152 170 2 2 76 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 152 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 3
  152 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 170 2 1 76 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 170 (accept_3_2 1
  152 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152 170))))))))))))))))))) (allB_succ' 20 151 170 (Eq.refl
  Bool.true) (allA_of_3_0 20 151 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 150 170 (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 150 170 10 2 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 170 (accept_3_2 19 150 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 170 2 9 75 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 170 (Polychromatic418967fa.accept_21_17_3_2_1_2111 17 150 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 170 2 8 75 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 150 170 5 3 30 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 170 2 7 75 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 170 (accept_3_2 13 150 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 170 2 6 75 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 150 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 170 10 1 15 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 170
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 150 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 150 170 2 4 75 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 170 (accept_3_2 7 150 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150
  170 2 3 75 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 150
  170 5 1 30 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 150
  170 2 2 75 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  150 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 150 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 150 170 2 1 75 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 150 170 (accept_3_2 1 150 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  170))))))))))))))))))))) (allB_succ' 22 149 170 (Eq.refl Bool.true) (allA_succ_of_accept 21 149 170
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 149 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 149 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 149 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 170 (accept_3_2 19 149 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 149 170 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 149 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 170
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 149 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 170 (accept_3_2 16 149 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 149 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 170 (Polychromatic418967fa.accept_16_14_5_10_1_3622 14 149 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 170 (accept_3_2 13 149 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 149 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 149 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 170 (accept_3_2 10 149 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 170 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 149 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 170 (accept_3_2 7 149 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 149 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 170
  (Polychromatic418967fa.accept_13_5_6_1_1_822 5 149 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 170 (accept_3_2 4 149 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 149 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 149 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 170 (accept_3_2 1 149 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149 170)))))))))))))))))))))) (allB_succ' 23 148 170 (Eq.refl Bool.true) (allA_of_3_0
  23 148 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 147 170 (Eq.refl Bool.true) (allA_succ_of_accept 23
  147 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 147 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 147 170 (accept_3_2 22 147 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 147 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 147 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 147 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 170 (accept_3_2 19 147 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 170 (Polychromatic418967fa.accept_12_6_3_2_1_743
  18 147 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 147 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 170 (accept_3_2 16 147 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 147 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 170 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 147 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 170 (accept_3_2 13 147 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 170 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 147 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 170 (accept_3_2 10 147 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 147 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 170 (Polychromatic418967fa.accept_15_8_12_5_1_2987 8 147 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 170 (accept_3_2 7 147 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 147 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 147 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 170 (accept_3_2 4 147 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 170 (Polychromatic418967fa.accept_13_3_4_1_1_363 3 147 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 147 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 170 (accept_3_2 1 147 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147 170)))))))))))))))))))))))) (allB_succ' 25 146 170 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 146 170 2 12 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 146 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 170 2 11 73 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 170
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 146 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 170 2 10 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 170 (accept_3_2 19 146 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 170 2 9 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 146 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 146 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 170 2 8 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  146 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 146 170 2 7 73 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 146 170 (accept_3_2 13
  146 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 146 170 2 6 73 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 146 170
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 146 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 146 170 2 5 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 146 170 (Polychromatic418967fa.accept_15_9_11_5_1_1283 9 146 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 146 170 2 4 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 146 170 (accept_3_2 7 146 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 146 170 2 3 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 146 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 146 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 146 170 2 2 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 146 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 3
  146 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 170 2 1 73 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 170 (accept_3_2 1
  146 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146 170))))))))))))))))))))))))) (allB_succ' 26 145 170
  (Eq.refl Bool.true) (allA_of_3_0 26 145 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 144 170 (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 144 170 2 13 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 144 170 (accept_3_2 25 144 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 170 2 12 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 144 170 (Polychromatic418967fa.accept_14_9_4_2_1_983 23 144 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 170 2 11 72 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 170
  (Polychromatic418967fa.accept_20_1_4_10_1_3645 21 144 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 144 170 2 10 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 144 170 (accept_3_2 19 144 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 170 2 9 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 170 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 144 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 170 2 8 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 144 170
  (Polychromatic418967fa.accept_20_15_4_10_1_9538 15 144 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 144 170 2 7 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 144 170 (accept_3_2 13 144 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 170 2 6 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 144 170 (Polychromatic418967fa.accept_15_11_9_5_1_2974 11 144 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 170 2 5 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 170 (Polychromatic418967fa.accept_14_9_4_2_1_983 9
  144 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 170 2 4 72 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 170 (accept_3_2 7
  144 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 170 2 3 72 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 170
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 144 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 144 170 2 2 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 144 170 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 144 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 170 2 1 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 170 (accept_3_2 1 144 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 144 170))))))))))))))))))))))))))) (allB_succ' 28 143 170 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 143 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 143 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 143 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 170 (accept_3_2 25 143 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 170
  (Polychromatic418967fa.accept_19_5_10_18_1_2705 24 143 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 143 170 (Polychromatic418967fa.accept_18_5_17_8_1_2984 23 143 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 170 (accept_3_2 22 143 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 143 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 170
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 143 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 143 170 (accept_3_2 19 143 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 143 170 (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 143 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 143 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 170 (accept_3_2 16 143 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 170
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 143 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 170 (accept_3_2 13 143 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 143 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 170 (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 143 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 170 (accept_3_2 10 143 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 143 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 170
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 143 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 170 (accept_3_2 7 143 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 143 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 143 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 170 (accept_3_2 4 143 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 170
  (Polychromatic418967fa.accept_18_2_17_8_1_1893 2 143 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 170 (accept_3_2 1 143 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  170)))))))))))))))))))))))))))) (allB_succ' 29 142 170 (Eq.refl Bool.true) (allA_of_3_0 29 142 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 141 170 (Eq.refl Bool.true) (allA_succ_of_accept 29 141 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 141 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 170 (accept_3_2 28 141 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 141 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 170 (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 141 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 170 (accept_3_2 25 141 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 141 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 141 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 170 (accept_3_2 22 141 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 141 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 141 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 170 (accept_3_2 19 141 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 170 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 141 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 170 (accept_3_2 16 141 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 141 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 141 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 141 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 170 (accept_3_2 13 141 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 141 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 141 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 170 (accept_3_2 10 141 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 170 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 141 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 170 (Polychromatic418967fa.accept_13_8_11_1_1_3789 8 141 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 170 (accept_3_2 7 141 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 141 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 170 (accept_3_2 4 141 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 141 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 170 (accept_3_2 1 141 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141 170)))))))))))))))))))))))))))))) (allB_succ' 31 140 170 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 140 170 10 3 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 140 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 140 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 170 2 14 70 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 170
  (Polychromatic418967fa.accept_16_11_12_10_1_3641 27 140 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 140 170 2 13 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 140 170 5 5 28 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 140 170 2 12 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 140 170 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 140
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 170 2 11 70 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 170
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 140 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 140 170 10 2 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 140 170 (accept_3_2 19 140 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 140 170 2 9 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 140 170 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 140 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 170 2 8 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 140 170 5 3 28 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 140 170 2 7 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 170 (accept_3_2 13 140 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 170 2 6 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 140 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 170 10 1 14 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 170
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 140 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 140 170 2 4 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 140 170 (accept_3_2 7 140 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140
  170 2 3 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 140
  170 5 1 28 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 140
  170 2 2 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  140 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 140 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 140 170 2 1 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 140 170 (accept_3_2 1 140 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  170))))))))))))))))))))))))))))))) (allB_succ' 32 139 170 (Eq.refl Bool.true) (allA_of_3_0 32 139 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 138 170 (Eq.refl Bool.true) (allA_succ_of_gcd 32 138 170 2 16 69 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 170
  (accept_3_2 31 138 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 138 170 2 15 69 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 138 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 138 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 138 170 2 14 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 138 170 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 138 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 138 170 2 13 69 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 170 (accept_3_2 25 138 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 138 170 2 12 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 138 170 (Polychromatic418967fa.accept_9_5_3_8_1_316 23
  138 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 170 2 11 69 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 170
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 138 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 138 170 2 10 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 170 (accept_3_2 19 138 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 170 2 9 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 138 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 170 2 8 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 15
  138 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 138 170 2 7 69 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 170 (accept_3_2 13
  138 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 170 2 6 69 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 170
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 138 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 170 2 5 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 138 170 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 138 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 138 170 2 4 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 170 (accept_3_2 7 138 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 138 170 2 3 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 138 170 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 138 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 170 2 2 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 138 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 3
  138 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 170 2 1 69 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 170 (accept_3_2 1
  138 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138 170))))))))))))))))))))))))))))))))) (allB_succ' 34 137
  170 (Eq.refl Bool.true) (allA_succ_of_accept 33 137 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 137 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 170
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 170 (accept_3_2 31 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 170 (Polychromatic418967fa.accept_13_3_7_1_1_334 29 137 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 170 (accept_3_2 28 137 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 137 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 170
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 170 (accept_3_2 25 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 137 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 170 (accept_3_2 22 137 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 170
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 170 (accept_3_2 19 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 170 (Polychromatic418967fa.accept_15_3_2_5_1_2980 18 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 170 (Polychromatic418967fa.accept_16_1_9_10_1_4740 17 137 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 170 (accept_3_2 16 137 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 137 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 170
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 170 (accept_3_2 13 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 137 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 170 (accept_3_2 10 137 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 137 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 170
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 170 (accept_3_2 7 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 137 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 170 (accept_3_2 4 137 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 137 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 170
  (Polychromatic418967fa.accept_19_2_4_18_1_9556 2 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 170 (accept_3_2 1 137 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  170)))))))))))))))))))))))))))))))))) (allB_succ' 35 136 170 (Eq.refl Bool.true) (allA_of_3_0 35 136 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 135 170 (Eq.refl Bool.true) (allA_succ_of_gcd 35 135 170 5 7 27 34
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 135 170
  (accept_3_2 34 135 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 135 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 135 170 (Polychromatic418967fa.accept_13_6_5_1_1_834 32 135 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 170 (accept_3_2 31 135 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 135 170 5 6 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 135 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 135 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 170 (accept_3_2 28 135 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 170 (Polychromatic418967fa.accept_20_7_15_10_1_3628 27 135
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 170
  (Polychromatic418967fa.accept_20_6_15_10_1_3555 26 135 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 135 170 5 5 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 135 170 (Polychromatic418967fa.accept_18_6_9_8_1_6812 24 135 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 170 (accept_3_2 22 135 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 135 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 135 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 135 170 5 4 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 135 170 (accept_3_2 19 135 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 135 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 135 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 135 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 170 (accept_3_2 16 135 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 170 5 3 27 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 170
  (Polychromatic418967fa.accept_16_14_7_10_1_898 14 135 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 170 (accept_3_2 13 135 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 135 170 (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 135 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 135 170 5 2 27 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 135 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 135 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 135 170 (Polychromatic418967fa.accept_11_8_3_5_1_355 8 135 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 170 (accept_3_2 7 135 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 135 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 135 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 135 170 5 1 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 135 170 (accept_3_2 4 135 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 170 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 135 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 170
  (Polychromatic418967fa.accept_20_2_15_10_1_5036 2 135 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 170 (accept_3_2 1 135 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  170)))))))))))))))))))))))))))))))))))) (allB_succ' 37 134 170 (Eq.refl Bool.true) (allA_succ_of_gcd 36 134 170 2 18
  67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 134 170
  (Polychromatic418967fa.accept_20_15_14_10_1_2317 35 134 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 134 170 2 17 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 134 170 (Polychromatic418967fa.accept_19_14_1_18_1_5280 33 134 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 134 170 2 16 67 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 134 170 (accept_3_2 31
  134 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 134 170 2 15 67 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 134 170
  (Polychromatic418967fa.accept_13_3_4_1_1_363 29 134 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 134 170 2 14 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 134 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 134 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 134 170 2 13 67 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 134 170 (accept_3_2 25 134 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 134 170 2 12 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 134 170 (Polychromatic418967fa.accept_13_10_4_1_1_2142
  23 134 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 170 2 11 67 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 170
  (Polychromatic418967fa.accept_15_6_14_5_1_2976 21 134 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 170 2 10 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 170 (accept_3_2 19 134 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 170 2 9 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 134 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 134 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 170 2 8 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 170 (Polychromatic418967fa.accept_14_1_8_2_1_1675
  15 134 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 134 170 2 7 67 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 134 170
  (accept_3_2 13 134 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 134 170 2 6 67 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 134 170
  (Polychromatic418967fa.accept_19_11_1_18_1_5276 11 134 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 134 170 2 5 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 134 170 (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 134 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 134 170 2 4 67 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 134 170 (accept_3_2 7 134 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134 170 2 3 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 134 170 (Polychromatic418967fa.accept_13_5_4_1_1_364 5 134 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 134 170 2 2 67 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 134 170
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 134 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 134 170 2 1 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 134 170 (accept_3_2 1 134 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  170))))))))))))))))))))))))))))))))))))) (allB_succ' 38 133 170 (Eq.refl Bool.true) (allA_of_3_0 38 133 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 132 170 (Eq.refl Bool.true) (allA_succ_of_gcd 38 132 170 2 19 66 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 170
  (accept_3_2 37 132 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 132 170 2 18 66 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 132 170
  (Polychromatic418967fa.accept_13_9_2_1_1_813 35 132 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 132 170 2 17 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 132 170 (Polychromatic418967fa.accept_20_13_12_10_1_3619 33 132 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 170 2 16 66 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 170 (accept_3_2 31 132 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 170 2 15 66 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 170
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 132 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 170 2 14 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 132 170 (Polychromatic418967fa.accept_18_9_6_8_1_2989 27 132 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 170 2 13 66 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 170 (accept_3_2 25 132 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 170 2 12 66 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 170
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 132 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 132 170 2 11 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 132 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 132 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 132 170 2 10 66 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 170 (accept_3_2 19 132 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 170 2 9 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 17
  132 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 170 2 8 66 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 170
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 132 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 132 170 2 7 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 132 170 (accept_3_2 13 132 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  132 170 2 6 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 132 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 132 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 132 170 2 5 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 132 170 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 132 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 170 2 4 66 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 170 (accept_3_2 7 132 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 170 2 3 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 132 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 170 2 2 66 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 132 170
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 132 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 132 170 2 1 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 132 170 (accept_3_2 1 132 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  170))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 131 170 (Eq.refl Bool.true) (allA_succ_of_accept 39 131 170
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 131 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 131 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 170 (accept_3_2 37 131 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 131 170 (Polychromatic418967fa.accept_15_6_11_5_1_168 36 131 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 170
  (Polychromatic418967fa.accept_14_7_5_2_1_2473 35 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 170 (accept_3_2 34 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 131 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 170 (accept_3_2 31 131 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 131 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 170 (accept_3_2 28 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 170 (Polychromatic418967fa.accept_11_4_10_5_1_1202 26 131 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 170 (accept_3_2 25 131 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 131 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 170
  (Polychromatic418967fa.accept_15_8_11_5_1_169 23 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 170 (accept_3_2 22 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 131 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 170 (accept_3_2 19 131 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 131 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 170 (accept_3_2 16 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 170 (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 131 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 170 (accept_3_2 13 131 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 131 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 170
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 170 (accept_3_2 10 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 170 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 131 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 170 (accept_3_2 7 131 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 131 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 170 (accept_3_2 4 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 131 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 170 (accept_3_2 1 131 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 170)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 130 170 (Eq.refl
  Bool.true) (allA_of_3_0 41 130 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 129 170 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 129 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 129 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 170 (accept_3_2 40 129 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 129 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 129 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 170 (Polychromatic418967fa.accept_9_2_3_8_1_318
  38 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 170 (accept_3_2 37
  129 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 170
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 129 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 129 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 170 (accept_3_2 34 129 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 129 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 129 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 170 (Polychromatic418967fa.accept_9_5_3_8_1_316
  32 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 170 (accept_3_2 31
  129 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 170
  (Polychromatic418967fa.accept_12_6_9_2_1_311 30 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 129 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 170 (accept_3_2 28 129 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 129 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 129 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 170 (Polychromatic418967fa.accept_7_5_3_2_1_249
  26 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 170 (accept_3_2 25
  129 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 170
  (Polychromatic418967fa.accept_9_6_3_8_1_595 24 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 129 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 129 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 170 (accept_3_2 22 129 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 129 170 (Polychromatic418967fa.accept_13_8_12_1_1_4662 21 129 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 170
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 170 (accept_3_2 19 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 170 (accept_3_2 16 129 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 129 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 170
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 170 (accept_3_2 13 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 129 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 170 (accept_3_2 10 129 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 170 (Polychromatic418967fa.accept_16_9_1_10_1_3610 9 129 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 170
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 170 (accept_3_2 7 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 170 (accept_3_2 4 129 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 129 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 170 (accept_3_2 1 129 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  170)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 128 170 (Eq.refl Bool.true) (allA_succ_of_gcd 42 128 170
  2 21 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 128
  170 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 128 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 128 170 2 20 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 128 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 128 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 128 170 2 19 64 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 128 170 (accept_3_2 37 128 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 128 170 2 18 64 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 128 170
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 128 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 128 170 2 17 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 128 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 128 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 128 170 2 16 64 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 128 170 (accept_3_2 31 128 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 128 170 2 15 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 128 170 (Polychromatic418967fa.accept_12_5_8_2_1_309
  29 128 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 170 2 14 64 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 170
  (Polychromatic418967fa.accept_15_12_8_5_1_5048 27 128 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 170 2 13 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 170 (accept_3_2 25 128 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 170 2 12 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 128 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 128 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 170 2 11 64 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 170
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 128 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 170 2 10 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 128 170 (accept_3_2 19 128 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 128 170 2 9 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 128 170 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 128 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 170 2 8 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 15
  128 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 170 2 7 64 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 170 (accept_3_2 13
  128 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 170 2 6 64 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 170
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 128 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 128 170 2 5 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 128 170 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 128 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 170 2 4 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 170 (accept_3_2 7 128 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 128 170 2 3 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 128 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 128 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 170 2 2 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  128 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 170 2 1 64 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 170 (accept_3_2 1
  128 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128 170)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 127 170 (Eq.refl Bool.true) (allA_of_3_0 44 127 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 45 126 170 (Eq.refl Bool.true) (allA_succ_of_gcd 44 126 170 2 22 63 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 170 (accept_3_2 43 126 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 126 170 2 21 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 126 170 (Polychromatic418967fa.accept_13_2_9_1_1_67 41
  126 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 170 2 20 63 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 126 170
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 126 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 126 170 2 19 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 126 170 (accept_3_2 37 126 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 170 2 18 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 170 (Polychromatic418967fa.accept_20_15_6_10_1_9569 35 126 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 170 2 17 63 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 170
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 126 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 170 2 16 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 170 (accept_3_2 31 126 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 170 2 15 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 170 (Polychromatic418967fa.accept_15_14_6_5_1_7215 29 126 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 170 2 14 63 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 170
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 126 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 170 2 13 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 170 (accept_3_2 25 126 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 170 2 12 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 170 (Polychromatic418967fa.accept_13_10_9_1_1_5609 23 126 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 170 2 11 63 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 126 170
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 126 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 126 170 2 10 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 170 (accept_3_2 19 126 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 170 2 9 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 170 (Polychromatic418967fa.accept_19_17_12_18_1_5248 17 126 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 170 2 8 63 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 170
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 126 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 126 170 2 7 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 126 170 (accept_3_2 13 126 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  126 170 2 6 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 126 170 (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 126 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 126 170 2 5 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 126 170 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 126 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 170 2 4 63 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 170 (accept_3_2 7 126 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 170 2 3 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 170 (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 126 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 170 2 2 63 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 126 170
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 126 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 126 170 2 1 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 126 170 (accept_3_2 1 126 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  170))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 125 170 (Eq.refl Bool.true) (allA_succ_of_gcd 45 125
  170 5 9 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  125 170 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 125 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 125 170 (accept_3_2 43 125 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 125 170 (Polychromatic418967fa.accept_19_4_11_18_1_3909 42 125 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 170
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 41 125 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 125 170 5 8 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 125 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 125 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 125 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 170 (accept_3_2 37 125 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 36
  125 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 125 170 5 7 25 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 125 170 (accept_3_2 34
  125 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 170
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 125 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 125 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 125 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 170 (accept_3_2 31 125 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 125 170 5 6 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 125 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 125 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 170 (accept_3_2 28 125 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 125 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 170
  (Polychromatic418967fa.accept_19_7_11_18_1_6680 26 125 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 125 170 5 5 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 125 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 125 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 125 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 125 170 (accept_3_2 22 125 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 125 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 125 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 125 170 5 4 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 125 170 (accept_3_2 19 125 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 125 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 125 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 125 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 170 (accept_3_2 16 125 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 125 170 5 3 25 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 125 170
  (Polychromatic418967fa.accept_16_14_13_10_1_2624 14 125 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 125 170 (accept_3_2 13 125 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 125 170 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 125 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 125 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 125 170 5 2 25 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 125 170
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 125 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 125 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 170 (accept_3_2 7 125 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 125 170 (Polychromatic418967fa.accept_13_6_8_1_1_2913 6 125 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 125 170 5 1 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 125 170 (accept_3_2 4 125 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 125 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 170
  (Polychromatic418967fa.accept_18_2_17_8_1_1893 2 125 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 170 (accept_3_2 1 125 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  170)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 124 170 (Eq.refl Bool.true) (allA_of_3_0 47 124 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 123 170 (Eq.refl Bool.true) (allA_succ_of_accept 47 123 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 170 (accept_3_2 46 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 123 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 123 170 (Polychromatic418967fa.accept_13_5_6_1_1_822 44 123 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 170 (accept_3_2 43 123 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 123
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 170 (accept_3_2 40 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 123 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 123 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 123 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 170 (accept_3_2 37 123 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 170 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 123 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 170 (accept_3_2 34 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 123 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 170 (accept_3_2 31 123 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 123 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 170 (accept_3_2 28 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 123 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 170 (accept_3_2 25 123 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 170 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 123 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 170 (accept_3_2 22 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 123 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 170 (accept_3_2 19 123 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 123 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 170 (accept_3_2 16 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 170 (Polychromatic418967fa.accept_13_2_6_1_1_3807 15 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 123 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 170 (accept_3_2 13 123 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 123 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 170 (accept_3_2 10 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 170 (Polychromatic418967fa.accept_11_8_2_5_1_1769 8 123 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 170 (accept_3_2 7 123 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 123 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 170 (accept_3_2 4 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 123 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 123 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 170 (accept_3_2 1 123 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 170)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 122 170 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 122 170 2 24 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 122 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 122 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 170 2 23 61 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 170
  (Polychromatic418967fa.accept_13_6_5_1_1_834 45 122 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 170 2 22 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 170 (accept_3_2 43 122 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 170 2 21 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 122 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 170 2 20 61 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 170
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 122 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 170 2 19 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 170 (accept_3_2 37 122 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 170 2 18 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 170 (Polychromatic418967fa.accept_13_9_5_1_1_1382 35 122 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 170 2 17 61 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 170
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 122 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 170 2 16 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 170 (accept_3_2 31 122 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 170 2 15 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 122 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 170 2 14 61 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 170
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 122 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 170 2 13 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 170 (accept_3_2 25 122 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 170 2 12 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 170 (Polychromatic418967fa.accept_18_5_14_8_1_2966 23 122 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 170 2 11 61 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 170
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 122 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 170 2 10 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 170 (accept_3_2 19 122 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 170 2 9 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 122 170 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 122 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 170 2 8 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  122 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 170 2 7 61 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 170 (accept_3_2 13
  122 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 170 2 6 61 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 170
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 122 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 122 170 2 5 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 122 170 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 122 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 170 2 4 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 170 (accept_3_2 7 122 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 122 170 2 3 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 122 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 122 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 170 2 2 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 3
  122 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 170 2 1 61 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 170 (accept_3_2 1
  122 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122 170)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 121 170 (Eq.refl Bool.true) (allA_of_3_0 50 121 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 51 120 170 (Eq.refl Bool.true) (allA_succ_of_gcd 50 120 170 10 5 12 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 170 (accept_3_2 49 120 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 120 170 2 24 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 120 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 47
  120 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 170 2 23 60 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 120 170 5 9 24 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 120 170 2 22 60 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 170
  (accept_3_2 43 120 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 170 2 21 60 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 170
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 120 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 170 10 4 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 120 170 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 120 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 120 170 2 19 60 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 170 (accept_3_2 37 120 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 170 2 18 60 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 120 170 5 7 24 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 120 170 2 17 60 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 170
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 120 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 120 170 2 16 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 120 170 (accept_3_2 31 120 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 170 10 3 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 120 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 170 2 14 60 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 120 170
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 120 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 120 170 2 13 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 120 170 5 5 24 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 120 170 2 12 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 120 170 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 120 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 170 2 11 60 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 170
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 21 120 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 170 10 2 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 120 170 (accept_3_2 19 120 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 170 2 9 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 120 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 170 2 8 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 120 170 5 3 24 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 120 170 2 7 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 170 (accept_3_2 13 120 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 170 2 6 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 120 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 170 10 1 12 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 170
  (Polychromatic418967fa.accept_19_9_6_18_1_730 9 120 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 170 2 4 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 170 (accept_3_2 7 120 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120
  170 2 3 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 120
  170 5 1 24 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 120
  170 2 2 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  120 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 120 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 120 170 2 1 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 120 170 (accept_3_2 1 120 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  170))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 119 170 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  119 170 17 3 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  50 119 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 119 170 (accept_3_2 49 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 119 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 119 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 170 (Polychromatic418967fa.accept_14_5_7_2_1_468 47 119
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 170 (accept_3_2 46 119
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 170 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 170
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 170 (accept_3_2 43 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 119 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 170 (accept_3_2 40 119 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 119 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 170
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 38 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 170 (accept_3_2 37 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 170 (Polychromatic418967fa.accept_15_6_14_5_1_2976 36 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 170 (Polychromatic418967fa.accept_13_9_2_1_1_813 35 119 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 119 170 17 2 7 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 119 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 119 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 119 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 170 (accept_3_2 31 119 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 119 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 119 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 29
  119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 170 (accept_3_2 28
  119 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 170
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 119 170 (Polychromatic418967fa.accept_14_12_7_2_1_1663 26 119 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 170 (accept_3_2 25 119 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 119 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 119 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 170 (Polychromatic418967fa.accept_9_5_2_8_1_109
  23 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 170 (accept_3_2 22
  119 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 119 170 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 119 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 170 (accept_3_2 19 119 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 119 170 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 119 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 17 119 170 17 1 7 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 119 170 (accept_3_2 16 119 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 170
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 170 (accept_3_2 13 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 170 (Polychromatic418967fa.accept_20_11_19_10_1_3568 11 119 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 170 (accept_3_2 10 119 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 119 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 170
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 170 (accept_3_2 7 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 119 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 170 (accept_3_2 4 119 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 170
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 170 (accept_3_2 1 119 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  170)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 118 170 (Eq.refl Bool.true) (allA_of_3_0 53 118
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 117 170 (Eq.refl Bool.true) (allA_succ_of_accept 53 117
  170 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 117 170 (accept_3_2 52 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 117 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 117 170 (Polychromatic418967fa.accept_23_4_2_9_1_9568 50 117 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 170 (accept_3_2 49 117 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 170 (Polychromatic418967fa.accept_20_8_17_10_1_8016 48 117
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 170 (accept_3_2 46 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 170 (Polychromatic418967fa.accept_16_12_5_10_1_3561 44 117 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 170 (accept_3_2 43 117 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 170 (Polychromatic418967fa.accept_11_9_7_5_1_749 42 117
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 170 (accept_3_2 40 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 117 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 117 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 117 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 170 (accept_3_2 37 117 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 170 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 117 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 170 (accept_3_2 34 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 170 (Polychromatic418967fa.accept_19_14_3_18_1_6675 33 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 117 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 170 (accept_3_2 31 117 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 117 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 170 (accept_3_2 28 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 117 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 117 170 (Polychromatic418967fa.accept_25_1_17_20_1_9567 26 117 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 170 (accept_3_2 25 117 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 117 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 170 (accept_3_2 22 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 117 170 (Polychromatic418967fa.accept_14_7_5_2_1_2473 21 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 170 (Polychromatic418967fa.accept_11_9_7_5_1_749 20 117 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 170 (accept_3_2 19 117 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 117 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 170 (accept_3_2 16 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 117 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 117 170 (Polychromatic418967fa.accept_16_14_5_10_1_3622 14 117 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 170 (accept_3_2 13 117 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 170 (Polychromatic418967fa.accept_16_12_5_10_1_3561 12 117
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 170 (accept_3_2 10 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  117 170 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 170 (Polychromatic418967fa.accept_15_8_12_5_1_2987 8 117 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 170 (accept_3_2 7 117 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 117 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 170 (accept_3_2 4 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 117 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 170 (Polychromatic418967fa.accept_15_2_12_5_1_2107 2 117 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 170 (accept_3_2 1 117 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117 170)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55
  116 170 (Eq.refl Bool.true) (allA_succ_of_gcd 54 116 170 2 27 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 116 170 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 116 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 170 2 26 58 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 170
  (Polychromatic418967fa.accept_14_9_4_2_1_983 51 116 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 170 2 25 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 170 (accept_3_2 49 116 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 170 2 24 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 116 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 170 2 23 58 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 170
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 116 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 170 2 22 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 170 (accept_3_2 43 116 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 170 2 21 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 116 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 170 2 20 58 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 170
  (Polychromatic418967fa.accept_15_9_11_5_1_1283 39 116 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 170 2 19 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 170 (accept_3_2 37 116 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 170 2 18 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 116 170 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 116 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 170 2 17 58 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 170
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 116 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 116 170 2 16 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 116 170 (accept_3_2 31 116 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 116 170 2 15 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 116 170 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 116 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 170 2 14 58 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 170
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 116 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 116 170 2 13 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 116 170 (accept_3_2 25 116 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 116 170 2 12 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 116 170 (Polychromatic418967fa.accept_11_1_6_5_1_1732 23 116 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 170 2 11 58 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 170
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 116 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 170 2 10 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 116 170 (accept_3_2 19 116 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 116 170 2 9 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 116 170 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 116 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 170 2 8 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 170 (Polychromatic418967fa.accept_13_2_12_1_1_343
  15 116 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 170 2 7 58 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 170
  (accept_3_2 13 116 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 170 2 6 58 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 170
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 116 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 116 170 2 5 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 116 170 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 116 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 170 2 4 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 170 (accept_3_2 7 116 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 116 170 2 3 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 116 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 116 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 170 2 2 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 170 (Polychromatic418967fa.accept_19_3_2_18_1_9566
  3 116 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 170 2 1 58 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 170 (accept_3_2 1
  116 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  170))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 115 170 (Eq.refl Bool.true) (allA_of_3_0 56
  115 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 114 170 (Eq.refl Bool.true) (allA_succ_of_gcd 56 114
  170 2 28 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55
  114 170 (accept_3_2 55 114 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 114 170 2 27 57 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 114 170
  (Polychromatic418967fa.accept_21_11_9_2_1_6354 53 114 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 114 170 2 26 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 114 170 (Polychromatic418967fa.accept_12_3_6_2_1_747 51 114 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 114 170 2 25 57 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 170 (accept_3_2 49 114 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 114 170 2 24 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 114 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 47
  114 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 170 2 23 57 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 114 170
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 114 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 114 170 2 22 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 114 170 (accept_3_2 43 114 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 170 2 21 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 114 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 170 2 20 57 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 170
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 114 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 170 2 19 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 170 (accept_3_2 37 114 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 170 2 18 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 170 (Polychromatic418967fa.accept_13_9_10_1_1_1389 35 114 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 170 2 17 57 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 170
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 114 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 170 2 16 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 170 (accept_3_2 31 114 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 170 2 15 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 114 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 170 2 14 57 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 170
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 114 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 170 2 13 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 170 (accept_3_2 25 114 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 170 2 12 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 114 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 170 2 11 57 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 170
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 114 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 170 2 10 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 170 (accept_3_2 19 114 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 170 2 9 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 170 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 114 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 170 2 8 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 170 (Polychromatic418967fa.accept_12_3_6_2_1_747
  15 114 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 114 170 2 7 57 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 170
  (accept_3_2 13 114 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 170 2 6 57 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 170
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 114 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 114 170 2 5 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 114 170 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 114 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 114 170 2 4 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 170 (accept_3_2 7 114 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 114 170 2 3 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 114 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 114 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 170 2 2 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 114 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  114 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 170 2 1 57 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 170 (accept_3_2 1
  114 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  170))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 113 170 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 113 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 113 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 113 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 170 (accept_3_2 55 113 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 170 (Polychromatic418967fa.accept_13_2_9_1_1_67
  54 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 170
  (Polychromatic418967fa.accept_18_17_5_8_1_1898 53 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 170 (accept_3_2 52 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 170 (Polychromatic418967fa.accept_13_11_9_1_1_1407 50 113 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 170 (accept_3_2 49 113 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 113 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 170 (accept_3_2 46 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 170 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 113 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 170 (accept_3_2 43 113 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 113 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 170
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 170 (accept_3_2 40 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 113 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 170 (accept_3_2 37 113 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 170 (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 113 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 170 (accept_3_2 34 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 170 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 113 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 170 (accept_3_2 31 113 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 113 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 170
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 170 (accept_3_2 28 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 170 (Polychromatic418967fa.accept_15_11_8_5_1_1278 26 113 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 170 (accept_3_2 25 113 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 113 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 170 (accept_3_2 22 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 113 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 170 (accept_3_2 19 113 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 170 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 113 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 170
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 170 (accept_3_2 16 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 170 (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 113 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 170 (accept_3_2 13 113 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 113 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 170 (accept_3_2 10 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 170 (Polychromatic418967fa.accept_11_8_3_5_1_355 8 113 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 170 (accept_3_2 7 113 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 113 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 170
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 170 (accept_3_2 4 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 113 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 113 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 170 (accept_3_2 1 113 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 112
  170 (Eq.refl Bool.true) (allA_of_3_0 59 112 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 111 170
  (Eq.refl Bool.true) (allA_succ_of_accept 59 111 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 111 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 170 (accept_3_2 58 111 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 111 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 111 170 (accept_3_2 55 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 111 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 111 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 170 (accept_3_2 52 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 111 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 170
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 170 (accept_3_2 49 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 111 170 (Polychromatic418967fa.accept_15_3_6_5_1_2079 48 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 111 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 170 (accept_3_2 46 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 111 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 170
  (Polychromatic418967fa.accept_15_14_6_5_1_7215 44 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 170 (accept_3_2 43 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 111 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 111 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 170 (accept_3_2 40 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 111 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 170
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 170 (accept_3_2 37 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 111 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 170 (accept_3_2 34 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 111 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 170
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 170 (accept_3_2 31 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 111 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 111 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 170 (accept_3_2 28 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 170 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 111 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 170
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 170 (accept_3_2 25 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 111 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 111 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 170 (accept_3_2 22 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 111 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 170 (accept_3_2 19 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 111 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 111 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 170 (accept_3_2 16 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 111 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 170
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 170 (accept_3_2 13 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 111 170 (Polychromatic418967fa.accept_15_12_6_5_1_1275 12 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 170 (accept_3_2 10 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 170
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 170 (accept_3_2 7 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 170 (accept_3_2 4 111 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 111 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 170 (accept_3_2 1 111 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 110 170 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 110 170 10 6 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 110 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 170 2 29 55 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 170
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 110 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 170 2 28 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 110 170 5 11 22 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 110 170 2 27 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 110 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 110 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 170 2 26 55 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 170
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 110 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 170 10 5 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 170 (accept_3_2 49 110 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 170 2 24 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 170 (Polychromatic418967fa.accept_13_8_6_1_1_3808 47 110 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 170 2 23 55 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 110 170 5 9 22 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 110 170 2 22 55 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 110 170 (accept_3_2 43
  110 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 110 170 2 21 55 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 110 170
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 110 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 110 170 10 4 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 110 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 110 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 110 170 2 19 55 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 110 170 (accept_3_2 37 110 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 110 170 2 18 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 110 170 5 7 22 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 110 170 2 17 55 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 170
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 110 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 170 2 16 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 170 (accept_3_2 31 110 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 170 10 3 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 170 (Polychromatic418967fa.accept_13_3_6_1_1_3797 29 110 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 170 2 14 55 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 170
  (Polychromatic418967fa.accept_23_4_18_9_1_9565 27 110 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 170 2 13 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 110 170 5 5 22 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 110 170 2 12 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 110 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 110 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 170 2 11 55 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 170
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 110 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 170 10 2 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 170 (accept_3_2 19 110 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 170 2 9 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 110 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 170 2 8 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 110 170 5 3 22 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 110 170 2 7 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 170 (accept_3_2 13 110 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 170 2 6 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 110 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 170 10 1 11 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 170
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 110 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 170 2 4 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 170 (accept_3_2 7 110 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  170 2 3 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 110
  170 5 1 22 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 110
  170 2 2 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  110 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 110 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 110 170 2 1 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 110 170 (accept_3_2 1 110 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 109 170 (Eq.refl Bool.true)
  (allA_of_3_0 62 109 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 108 170 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 108 170 2 31 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 108 170 (accept_3_2 61 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 170 2 30 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 170 (Polychromatic418967fa.accept_16_11_12_10_1_3641 59 108 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 170 2 29 54 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 108 170
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 108 170 2 28 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 108 170 (accept_3_2 55 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 170 2 27 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 170 (Polychromatic418967fa.accept_15_8_3_5_1_608 53 108 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 170 2 26 54 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 108 170
  (Polychromatic418967fa.accept_11_7_9_5_1_338 51 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 108 170 2 25 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 108 170 (accept_3_2 49 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 170 2 24 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 108 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 170 2 23 54 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 108 170
  (Polychromatic418967fa.accept_16_13_12_10_1_3540 45 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 108 170 2 22 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 108 170 (accept_3_2 43 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 170 2 21 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 108 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 170 2 20 54 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 108 170
  (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 108 170 2 19 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 108 170 (accept_3_2 37 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 170 2 18 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 108 170 (Polychromatic418967fa.accept_16_3_12_10_1_315 35 108 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 170 2 17 54 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 170
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 108 170 2 16 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 108 170 (accept_3_2 31 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 170 2 15 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 108 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 170 2 14 54 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 108 170
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 108 170 2 13 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 108 170 (accept_3_2 25 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 170 2 12 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 108 170 (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 108 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 170 2 11 54 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 170
  (Polychromatic418967fa.accept_15_6_3_5_1_607 21 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 170 2 10 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 108 170 (accept_3_2 19 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 170 2 9 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 170 (Polychromatic418967fa.accept_15_2_3_5_1_2991 17 108 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 170 2 8 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  108 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 170 2 7 54 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 170 (accept_3_2 13
  108 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 170 2 6 54 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 170
  (Polychromatic418967fa.accept_16_11_12_10_1_3641 11 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 108 170 2 5 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 108 170 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 108 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 170 2 4 54 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 170 (accept_3_2 7 108 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 170 2 3 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 108 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 170 2 2 54 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 170
  (Polychromatic418967fa.accept_13_3_4_1_1_363 3 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 108 170 2 1 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 170 (accept_3_2 1 108 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 107 170 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 107 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 107 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 170 (Polychromatic418967fa.accept_25_12_7_20_1_9564 62 107
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 170 (accept_3_2 61 107
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 170
  (Polychromatic418967fa.accept_14_4_9_2_1_95 60 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 107 170 (Polychromatic418967fa.accept_13_7_3_1_1_814 59 107 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 170 (accept_3_2 58 107 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 107 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 107 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 170
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 170 (accept_3_2 55 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 170 (Polychromatic418967fa.accept_13_2_3_1_1_3823 54 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 107 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 170 (accept_3_2 52 107 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 107 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 170
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 50 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 170 (accept_3_2 49 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 170 (Polychromatic418967fa.accept_15_3_2_5_1_2980 48 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 170 (Polychromatic418967fa.accept_11_3_8_5_1_336 47 107 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 170 (accept_3_2 46 107 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 107 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 170
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 170 (accept_3_2 43 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 170 (Polychromatic418967fa.accept_15_12_2_5_1_3939 42 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 107 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 170 (accept_3_2 40 107 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 170
  (Polychromatic418967fa.accept_18_2_17_8_1_1893 38 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 170 (accept_3_2 37 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 170 (Polychromatic418967fa.accept_11_3_8_5_1_336 36 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 170 (Polychromatic418967fa.accept_11_2_8_5_1_1219 35 107 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 170 (accept_3_2 34 107 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 107 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 170
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 170 (accept_3_2 31 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 170 (Polychromatic418967fa.accept_13_4_3_1_1_2898 30 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 107 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 170 (accept_3_2 28 107 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 170
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 26 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 170 (accept_3_2 25 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 170 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 170 (Polychromatic418967fa.accept_18_5_17_8_1_2984 23 107 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 170 (accept_3_2 22 107 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 107 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 170
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 170 (accept_3_2 19 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 170 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 107 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 170 (accept_3_2 16 107 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 170
  (Polychromatic418967fa.accept_11_3_8_5_1_336 14 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 170 (accept_3_2 13 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 170 (Polychromatic418967fa.accept_15_12_2_5_1_3939 12 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 170 (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 107 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 170 (accept_3_2 10 107 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 170
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 170 (accept_3_2 7 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 170 (Polychromatic418967fa.accept_13_6_3_1_1_1413 6 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 170 (accept_3_2 4 107 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 170
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 2 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 170 (accept_3_2 1 107 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 106 170 (Eq.refl Bool.true)
  (allA_of_3_0 65 106 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 105 170 (Eq.refl Bool.true)
  (allA_succ_of_gcd 65 105 170 5 13 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 105 170 (accept_3_2 64 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 105 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 105 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 170 (Polychromatic418967fa.accept_19_5_10_18_1_2705 62 105
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 170 (accept_3_2 61 105
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 170 5 12 21 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 170 (accept_3_2 58 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 105 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 105 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 105 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 105 170 5 11 21 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 105 170
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 105 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 170 (accept_3_2 52 105 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 105 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 105 170 5 10 21 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 105 170 (accept_3_2 49 105 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 105 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 170 (accept_3_2 46 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  105 170 5 9 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 105 170 (Polychromatic418967fa.accept_20_4_5_10_1_2308 44 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 105 170 (accept_3_2 43 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 105 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 105 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 105 170 5 8 21 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 105 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 105 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 105 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 170 (accept_3_2 37 105 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 105 170 (Polychromatic418967fa.accept_19_17_10_18_1_9563 36 105 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 105 170 5 7 21 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 170 (accept_3_2 34 105 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 170 (Polychromatic418967fa.accept_14_5_7_2_1_468
  33 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 170
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 170 (accept_3_2 31 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  105 170 5 6 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 105 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 105 170 (accept_3_2 28 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 105 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 105 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 170 (Polychromatic418967fa.accept_14_12_7_2_1_1663 26 105
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 105 170 5 5 21 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 105 170
  (Polychromatic418967fa.accept_19_5_10_18_1_2705 24 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 105 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 170 (accept_3_2 22 105 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 105 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 105 170 5 4 21 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 105 170 (accept_3_2 19 105 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 170 (Polychromatic418967fa.accept_12_6_9_2_1_311
  18 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 170 (accept_3_2 16 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  105 170 5 3 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 105 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 105 170 (accept_3_2 13 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 105 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 105 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 105 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 105 170 5 2 21 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 105 170
  (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 170 (Polychromatic418967fa.accept_19_8_10_18_1_5232 8 105 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 170 (accept_3_2 7 105 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 105 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 105 170 5 1 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 170 (accept_3_2 4 105 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 170
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 170 (accept_3_2 1 105 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 104 170 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 104 170 2 33 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 104 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 104 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 104 170 2 32 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 104 170
  (Polychromatic418967fa.accept_19_6_9_18_1_8140 63 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 104 170 2 31 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 104 170 (accept_3_2 61 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 104 170 2 30 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 104 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 170 2 29 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 170
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 170 2 28 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 104 170 (accept_3_2 55 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 170 2 27 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 104 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 170 2 26 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 170
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 170 2 25 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 170 (accept_3_2 49 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 170 2 24 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 104 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 170 2 23 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 170
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 104 170 2 22 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 104 170 (accept_3_2 43 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 170 2 21 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 170 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 104 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 170 2 20 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 170
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 170 2 19 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 170 (accept_3_2 37 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 170 2 18 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 104 170 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 104 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 170 2 17 52 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 170
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 104 170 2 16 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 104 170 (accept_3_2 31 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 104 170 2 15 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 104 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 104 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 170 2 14 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 170
  (Polychromatic418967fa.accept_19_8_9_18_1_2704 27 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 104 170 2 13 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 104 170 (accept_3_2 25 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 170 2 12 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 104 170 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 104 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 170 2 11 52 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 170
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 170 2 10 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 104 170 (accept_3_2 19 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 104 170 2 9 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 104 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 170 2 8 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  104 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 170 2 7 52 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 170 (accept_3_2 13
  104 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 170 2 6 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 170
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 104 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 170 2 5 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 104 170 (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 104 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 170 2 4 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 170 (accept_3_2 7 104 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 104 170 2 3 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 104 170 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 104 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 170 2 2 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 3
  104 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 170 2 1 52 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 170 (accept_3_2 1
  104 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 103 170 (Eq.refl Bool.true)
  (allA_of_3_0 68 103 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 102 170 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 102 170 34 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 102 170 (accept_3_2 67 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66
  102 170 2 33 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 102 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 102 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 170 2 32 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 102 170 (Polychromatic418967fa.accept_11_8_3_5_1_355
  63 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 102 170 2 31 51 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 170
  (accept_3_2 61 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 102 170 2 30 51 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 102 170
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 102 170 2 29 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 102 170 (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 102 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 102 170 2 28 51 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 170 (accept_3_2 55 102 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 102 170 2 27 51 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 102 170
  (Polychromatic418967fa.accept_15_8_12_5_1_2987 53 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 102 170 2 26 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 102 170 17 3 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 102 170 2 25 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 102 170 (accept_3_2 49 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 170 2 24 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 102 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 170 2 23 51 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 170
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 170 2 22 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 170 (accept_3_2 43 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 170 2 21 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 102 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 170 2 20 51 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 170
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 170 2 19 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 170 (accept_3_2 37 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 170 2 18 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 170 (Polychromatic418967fa.accept_13_9_11_1_1_1375 35 102 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 170 34 1 3 5 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 170
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 170 2 16 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 170 (accept_3_2 31 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 170 2 15 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 102 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 170 2 14 51 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 170
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 170 2 13 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 170 (accept_3_2 25 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 170 2 12 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 170 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 102 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 170 2 11 51 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 170
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 170 2 10 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 170 (accept_3_2 19 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 170 2 9 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 17 102 170 17 1 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 16 102 170 2 8 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 102 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 102 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 170 2 7 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 170 (accept_3_2 13 102 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 170 2 6 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 102 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 170 2 5 51 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 170
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 170 2 4 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 170 (accept_3_2 7 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102
  170 2 3 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  102 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 102 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 170 2 2 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 102 170 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 102 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 170 2 1 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 170 (accept_3_2 1 102 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 102 170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 101 170 (Eq.refl Bool.true) (allA_succ_of_accept 69 101 170 (Polychromatic418967fa.accept_6_3_5_2_1_12
  69 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 170
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 170 (accept_3_2 67 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 170 (Polychromatic418967fa.accept_20_5_1_10_1_6523 65 101 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 170 (accept_3_2 64 101 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 101 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 170
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 101 170 (accept_3_2 61 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 101 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 170 (accept_3_2 58 101 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 101 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 170
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 170 (accept_3_2 55 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 170 (Polychromatic418967fa.accept_15_8_11_5_1_169 53 101 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 170 (accept_3_2 52 101 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 101 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 170
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 170 (accept_3_2 49 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 101 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 170 (accept_3_2 46 101 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 170
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 170 (accept_3_2 43 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 101 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 170 (accept_3_2 40 101 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 101 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 170
  (Polychromatic418967fa.accept_15_8_11_5_1_169 38 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 170 (accept_3_2 37 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 101 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 170 (accept_3_2 34 101 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 170
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 170 (accept_3_2 31 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 101 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 170 (accept_3_2 28 101 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 101 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 170
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 170 (accept_3_2 25 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 101 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 170 (accept_3_2 22 101 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 170
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 170 (accept_3_2 19 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 170 (Polychromatic418967fa.accept_22_18_13_16_1_9562 18 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 170 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 101 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 170 (accept_3_2 16 101 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 170
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 170 (accept_3_2 13 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 101 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 170 (accept_3_2 10 101 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 170
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 170 (accept_3_2 7 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 101 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 170 (accept_3_2 4 101 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 101 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 170
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 2 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 170 (accept_3_2 1 101 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 100 170 (Eq.refl Bool.true)
  (allA_of_3_0 71 100 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 99 170 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 99 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 99 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 170 (accept_3_2 70 99 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 99 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 170
  (Polychromatic418967fa.accept_19_11_4_18_1_5226 68 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 170 (accept_3_2 67 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 170 (accept_3_2 64 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 170 (Polychromatic418967fa.accept_13_11_8_1_1_3815 63 99 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 170
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 170 (accept_3_2 61 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 170 (Polychromatic418967fa.accept_16_12_3_10_1_3524 60 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 170 (accept_3_2 58 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 99 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 170
  (Polychromatic418967fa.accept_15_11_9_5_1_2974 56 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 170 (accept_3_2 55 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 170 (accept_3_2 52 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 170 (Polychromatic418967fa.accept_13_12_8_1_1_825 51 99 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 170
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 50 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 170 (accept_3_2 49 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 170 (accept_3_2 46 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 99 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 170
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 44 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 170 (accept_3_2 43 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 170 (accept_3_2 40 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 170 (Polychromatic418967fa.accept_16_7_3_10_1_3614 39 99 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 170
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 170 (accept_3_2 37 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 170 (Polychromatic418967fa.accept_14_8_1_2_1_965 36 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 170 (accept_3_2 34 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 99 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 170
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 32 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 170 (accept_3_2 31 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 170 (accept_3_2 28 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 99 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 170
  (Polychromatic418967fa.accept_15_11_9_5_1_2974 26 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 170 (accept_3_2 25 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 170 (accept_3_2 22 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 170
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 170 (accept_3_2 19 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 170 (accept_3_2 16 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 170 (Polychromatic418967fa.accept_19_15_4_18_1_5227 15 99 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 170
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 170 (accept_3_2 13 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 170 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 170 (accept_3_2 10 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 170
  (Polychromatic418967fa.accept_14_8_1_2_1_965 8 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 170 (accept_3_2 7 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  170 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 99 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 170 (accept_3_2 4 99 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 99 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 170 (Polychromatic418967fa.accept_19_2_4_18_1_9556
  2 99 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 170 (accept_3_2 1 99
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 98 170 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 98 170 2 36 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 98 170 (Polychromatic418967fa.accept_13_6_7_1_1_335 71 98 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 170 2 35 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 170 (Polychromatic418967fa.accept_21_6_14_2_1_7980
  69 98 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 98 170 2 34 49 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 98 170 (accept_3_2 67
  98 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 98 170 2 33 49 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 98 170
  (Polychromatic418967fa.accept_20_5_18_10_1_3565 65 98 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 98 170 2 32 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 98 170 (Polychromatic418967fa.accept_13_11_7_1_1_1386 63 98 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 98 170 2 31 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 98 170 (accept_3_2 61 98 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 98 170 2 30 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 98 170 (Polychromatic418967fa.accept_11_4_10_5_1_1202 59 98 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 98 170 2 29 49 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 98 170
  (Polychromatic418967fa.accept_15_12_8_5_1_5048 57 98 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 98 170 2 28 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 98 170 (accept_3_2 55 98 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 98
  170 2 27 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  98 170 (Polychromatic418967fa.accept_19_15_3_18_1_5241 53 98 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 98 170 2 26 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 98 170 (Polychromatic418967fa.accept_21_9_14_2_1_6370 51 98 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 98 170 2 25 49 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 98 170 (accept_3_2 49 98 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 98 170 2 24 49 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 98 170
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 47 98 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 98 170 2 23 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 98 170 (Polychromatic418967fa.accept_13_6_7_1_1_335 45 98 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 98 170 2 22 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 98 170 (accept_3_2 43 98 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98 170 2 21 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 98 170 (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 98 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 170 2 20 49 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 170
  (Polychromatic418967fa.accept_11_6_10_5_1_341 39 98 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 98 170 2 19 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 98 170 (accept_3_2 37 98 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 98
  170 2 18 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  98 170 (Polychromatic418967fa.accept_19_16_3_18_1_8120 35 98 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 98 170 2 17 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 98 170 (Polychromatic418967fa.accept_15_3_8_5_1_2105 33 98 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 98 170 2 16 49 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 98 170 (accept_3_2 31 98 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 98 170 2 15 49 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 98 170
  (Polychromatic418967fa.accept_13_3_7_1_1_334 29 98 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 98 170 2 14 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 98 170 (Polychromatic418967fa.accept_15_12_8_5_1_5048 27 98 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 98 170 2 13 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 98 170 (accept_3_2 25 98 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98 170 2 12 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 98 170 (Polychromatic418967fa.accept_19_4_3_18_1_2699 23 98 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 98 170 2 11 49 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 98 170
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 98 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 98 170 2 10 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 98 170 (accept_3_2 19 98 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98
  170 2 9 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  98 170 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 98 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 98 170 2 8 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 98 170 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 98 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 170 2 7 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 170 (accept_3_2 13 98 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98 170 2 6 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 98 170 (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 98 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 98 170 2 5 49 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 98 170
  (Polychromatic418967fa.accept_19_9_3_18_1_5263 9 98 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 98 170 2 4 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 98 170 (accept_3_2 7 98 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 170
  2 3 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 98
  170 (Polychromatic418967fa.accept_20_5_18_10_1_3565 5 98 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 98 170 2 2 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 98 170 (Polychromatic418967fa.accept_13_3_7_1_1_334 3 98 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 170 2 1 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 170 (accept_3_2 1 98 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 98 170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 74 97 170 (Eq.refl Bool.true) (allA_of_3_0 74 97 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  75 96 170 (Eq.refl Bool.true) (allA_succ_of_gcd 74 96 170 2 37 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 96 170 (accept_3_2 73 96 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 96 170 2 36 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 96 170 (Polychromatic418967fa.accept_13_6_5_1_1_834 71 96 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 170 2 35 48 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 96 170
  (Polychromatic418967fa.accept_11_3_8_5_1_336 69 96 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 96 170 2 34 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 96 170 (accept_3_2 67 96 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96
  170 2 33 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  96 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 96 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 96 170 2 32 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 96 170 (Polychromatic418967fa.accept_14_7_12_2_1_2502 63 96 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 170 2 31 48 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 170 (accept_3_2 61 96 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 170 2 30 48 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 170
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 96 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 96 170 2 29 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 96 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 96 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 96 170 2 28 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 170 (accept_3_2 55 96 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 170 2 27 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 96 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 170 2 26 48 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 96 170
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 51 96 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 96 170 2 25 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 96 170 (accept_3_2 49 96 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96
  170 2 24 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  96 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 96 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 96 170 2 23 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 96 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 96 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 96 170 2 22 48 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 170 (accept_3_2 43 96 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 170 2 21 48 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 170
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 96 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 96 170 2 20 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 96 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 96 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 170 2 19 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 170 (accept_3_2 37 96 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 170 2 18 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 170 (Polychromatic418967fa.accept_11_2_8_5_1_1219 35 96 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 170 2 17 48 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 170
  (Polychromatic418967fa.accept_15_3_6_5_1_2079 33 96 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 170 2 16 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 170 (accept_3_2 31 96 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96
  170 2 15 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  96 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 96 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 96 170 2 14 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 96 170 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 96 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 170 2 13 48 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 170 (accept_3_2 25 96 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 170 2 12 48 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 170
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 96 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 96 170 2 11 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 96 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 96 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 96 170 2 10 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 170 (accept_3_2 19 96 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 170 2 9 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 96 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 96 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 170 2 8 48 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 170
  (Polychromatic418967fa.accept_20_15_16_10_1_6480 15 96 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 96 170 2 7 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 96 170 (accept_3_2 13 96 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 170 2 6 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 96 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 170 2 5 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 170 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 96 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 170 2 4 48 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 170 (accept_3_2 7 96 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 170 2 3 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 170 2 2 48 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 96 170
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 96 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 96 170 2 1 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 170 (accept_3_2 1 96 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 95 170 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 95 170 5 15 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 95 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 95 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 170 (accept_3_2 73 95 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 170 (Polychromatic418967fa.accept_20_12_15_10_1_6520 72 95 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 170
  (Polychromatic418967fa.accept_18_17_5_8_1_1898 71 95 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 95 170 5 14 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 95 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 95 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 95 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 95 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 170 (accept_3_2 67 95 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 66
  95 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 95 170 5 13 19 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 95 170 (accept_3_2 64
  95 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 170
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 95 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 95 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 95 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 170 (accept_3_2 61 95 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 95 170 5 12 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 95 170 (Polychromatic418967fa.accept_16_11_15_10_1_3515 59 95 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 95 170 (accept_3_2 58 95 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 95 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 95 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 95 170
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 95 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 95 170 5 11 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 95 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 95 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 95 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 170 (accept_3_2 52 95 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 95 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 51
  95 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 95 170 5 10 19 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 95 170 (accept_3_2 49
  95 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 170
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 95 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 95 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 95 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 170 (accept_3_2 46 95 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 95 170 5 9 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 95 170 (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 95 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 170 (accept_3_2 43 95 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 95 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 95 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 95 170 5 8 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 95 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 95 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 170 (accept_3_2 37 95 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 170 (Polychromatic418967fa.accept_13_10_4_1_1_2142
  36 95 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 95 170 5 7 19 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 95 170 (accept_3_2 34
  95 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 95 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 95 170 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 95 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 170 (accept_3_2 31 95 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 95 170 5 6 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 95 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 95 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 170 (accept_3_2 28 95 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 170
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 95 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 95 170 5 5 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 95 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 95 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 170 (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 95
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 170 (accept_3_2 22 95 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  95 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 95 170 5 4 19 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 95 170 (accept_3_2 19
  95 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 170
  (Polychromatic418967fa.accept_13_5_4_1_1_364 18 95 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 95 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 95 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 170 (accept_3_2 16 95 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 95 170 5 3 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 95 170 (Polychromatic418967fa.accept_16_14_15_10_1_5910 14 95 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 170 (accept_3_2 13 95 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 95 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 170
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 95 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 95 170 5 2 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 95 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 95 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 170 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 95 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 170 (accept_3_2 7 95 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 6
  95 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 95 170 5 1 19 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 95 170 (accept_3_2 4 95
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 170 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 95 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 170
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 95 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 170 (accept_3_2 1 95 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 94 170 (Eq.refl
  Bool.true) (allA_of_3_0 77 94 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 93 170 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 93 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 93 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 170 (accept_3_2 76 93 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 93 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 74
  93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 170 (accept_3_2 73 93
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 93 170
  (Polychromatic418967fa.accept_20_12_13_10_1_8061 72 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 170 (accept_3_2 70 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 93 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 170
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 170 (accept_3_2 67 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 66 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 170 (accept_3_2 64 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 93 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 170
  (Polychromatic418967fa.accept_15_2_3_5_1_2991 62 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 170 (accept_3_2 61 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 170 (accept_3_2 58 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 170 (Polychromatic418967fa.accept_20_17_13_10_1_5059 57 93 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 170 (accept_3_2 55 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 170 (accept_3_2 52 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 93 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 170
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 170 (accept_3_2 49 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 170 (Polychromatic418967fa.accept_13_9_2_1_1_813 48 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 170 (accept_3_2 46 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 170 (Polychromatic418967fa.accept_13_6_2_1_1_2137 45 93 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 170
  (Polychromatic418967fa.accept_16_12_13_10_1_2637 44 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 93 170 (accept_3_2 43 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 93 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 93 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 170 (accept_3_2 40 93 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 170 (accept_3_2 37 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 170 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 170 (accept_3_2 34 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 93 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 170
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 170 (accept_3_2 31 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 170 (accept_3_2 28 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 170
  (Polychromatic418967fa.accept_19_7_17_18_1_8155 26 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 170 (accept_3_2 25 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 170 (accept_3_2 22 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 170 (Polychromatic418967fa.accept_14_7_9_2_1_2489 21 93 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 170 (accept_3_2 19 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 170 (accept_3_2 16 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 170
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 170 (accept_3_2 13 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 170 (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 170 (accept_3_2 10 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 170 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 93 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 170
  (Polychromatic418967fa.accept_15_8_3_5_1_608 8 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 170 (accept_3_2 7 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  170 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 170 (accept_3_2 4 93 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  93 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 170 (accept_3_2 1 93 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 92 170 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 92 170 2 39 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 92 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 92 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 92 170 2 38 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 92 170
  (Polychromatic418967fa.accept_9_3_2_8_1_108 75 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 92 170 2 37 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 92 170 (accept_3_2 73 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 92
  170 2 36 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71
  92 170 (Polychromatic418967fa.accept_12_11_8_2_1_1274 71 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 92 170 2 35 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 92 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 92 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 92 170 2 34 46 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 92 170 (accept_3_2 67 92 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92 170 2 33 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 92 170
  (Polychromatic418967fa.accept_11_10_4_5_1_359 65 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 92 170 2 32 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 92 170 (Polychromatic418967fa.accept_15_3_2_5_1_2980 63 92 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 170 2 31 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 170 (accept_3_2 61 92 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 170 2 30 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 92 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 92 170 2 29 46 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 92 170
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 92 170 2 28 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 92 170 (accept_3_2 55 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92
  170 2 27 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  92 170 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 92 170 2 26 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 92 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 92 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 92 170 2 25 46 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 92 170 (accept_3_2 49 92 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92 170 2 24 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 92 170
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 92 170 2 23 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 92 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 92 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 170 2 22 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 170 (accept_3_2 43 92 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 170 2 21 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 92 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 92 170 2 20 46 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 170
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 92 170 2 19 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 92 170 (accept_3_2 37 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92
  170 2 18 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  92 170 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 92 170 2 17 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 92 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 92 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 92 170 2 16 46 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 92 170 (accept_3_2 31 92 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92 170 2 15 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 92 170
  (Polychromatic418967fa.accept_12_5_8_2_1_309 29 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 92 170 2 14 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 92 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 92 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 170 2 13 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 170 (accept_3_2 25 92 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 170 2 12 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 92 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 92 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 170 2 11 46 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 170
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 170 2 10 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 92 170 (accept_3_2 19 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92
  170 2 9 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  92 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 92 170 2 8 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 92 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 92 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 170 2 7 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 170 (accept_3_2 13 92 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 170 2 6 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 92 170 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 92 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 170 2 5 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 170
  (Polychromatic418967fa.accept_19_9_16_18_1_3887 9 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 170 2 4 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 170 (accept_3_2 7 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 170
  2 3 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  170 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 92 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 92 170 2 2 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 92 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 92 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 170 2 1 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 170 (accept_3_2 1 92 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92 170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 91 170 (Eq.refl Bool.true) (allA_of_3_0 80 91 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  81 90 170 (Eq.refl Bool.true) (allA_succ_of_gcd 80 90 170 10 8 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 170 (accept_3_2 79 90 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 90 170 2 39 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 90 170 (Polychromatic418967fa.accept_19_1_14_18_1_3919 77 90 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 170 2 38 45 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 90 170 5 15 18 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 90 170 2 37 45 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 90 170 (accept_3_2 73 90 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 170 2 36 45 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 170
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 90 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 90 170 10 7 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 90 170 (Polychromatic418967fa.accept_12_9_6_2_1_1273 69 90 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 90 170 2 34 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 170 (accept_3_2 67 90 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 170 2 33 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 90 170 5 13 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 90 170 2 32 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 170 (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 90 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 90 170 2 31 45 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 170 (accept_3_2 61
  90 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 170 10 6 9 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 170
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 90 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 90 170 2 29 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 90 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 90 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 90 170 2 28 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 90 170 5 11 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 90 170 2 27 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 53
  90 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 170 2 26 45 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 170
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 90 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 170 10 5 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 170 (accept_3_2 49 90 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90
  170 2 24 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  90 170 (Polychromatic418967fa.accept_13_8_12_1_1_4662 47 90 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 90 170 2 23 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 90 170 5 9 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 90 170 2 22 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 90 170 (accept_3_2 43 90 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 170 2 21 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 90 170 (Polychromatic418967fa.accept_11_8_2_5_1_1769 41 90 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 170 10 4 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 90 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 170 2 19 45 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 170 (accept_3_2 37
  90 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 170 2 18 45 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 90 170 5 7 18 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 90 170 2 17 45 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 170
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 90 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 170 2 16 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 90 170 (accept_3_2 31 90 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90
  170 10 3 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  90 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 90 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 90 170 2 14 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 90 170 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 90 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 170 2 13 45 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 90 170 5 5 18 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 90 170 2 12 45 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 170
  (Polychromatic418967fa.accept_19_4_14_18_1_5234 23 90 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 170 2 11 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 90 170 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 90 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 170 10 2 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 170 (accept_3_2 19 90 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 90 170 2 9 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 90 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 90 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 170 2 8 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 170 5 3 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 170 2 7 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 170 (accept_3_2 13 90 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 170 2 6 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 90 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 90 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 170 10 1 9 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 170
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 90 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 90 170 2 4 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 170 (accept_3_2 7 90 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 170
  2 3 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 90 170 5
  1 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 90 170 2 2
  45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 170
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 90 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 170 2 1 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 170 (accept_3_2 1 90 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 89 170 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 89 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 89 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 80
  89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 170 (accept_3_2 79 89
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 170
  (Polychromatic418967fa.accept_22_12_1_16_1_3122 78 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 89 170 (Polychromatic418967fa.accept_13_12_11_1_1_2920 77 89 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 89 170 (accept_3_2 76 89 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 89 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 89 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 74
  89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 170 (accept_3_2 73 89
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 170
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 72 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 89 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 89 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 89 170 (accept_3_2 70 89 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 89 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 89 170 (Polychromatic418967fa.accept_12_8_5_2_1_746
  68 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 170 (accept_3_2 67
  89 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 170
  (Polychromatic418967fa.accept_7_3_5_2_1_17 66 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 89 170 (Polychromatic418967fa.accept_16_1_9_10_1_4740 65 89 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 89 170 (accept_3_2 64 89 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 89 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 89 170
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 62 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 89 170 (accept_3_2 61 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  89 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 89 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 89 170 (accept_3_2 58 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 89 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 89 170
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 89 170 (accept_3_2 55 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  89 170 (Polychromatic418967fa.accept_15_9_14_5_1_2086 54 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 89 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 89 170 (accept_3_2 52 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 89 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 89 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 89 170
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 50 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 89 170 (accept_3_2 49 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  89 170 (Polychromatic418967fa.accept_13_9_11_1_1_1375 48 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 89 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 89 170 (accept_3_2 46 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 89 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 89 170
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 89 170 (accept_3_2 43 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  89 170 (Polychromatic418967fa.accept_13_3_11_1_1_2122 42 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 89 170 (Polychromatic418967fa.accept_18_5_17_8_1_2984 41 89 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 89 170 (accept_3_2 40 89 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 89 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 89 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 170
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 89 170 (accept_3_2 37 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  89 170 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 89 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 89 170 (accept_3_2 34 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 89 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 170
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 89 170 (accept_3_2 31 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  89 170 (Polychromatic418967fa.accept_29_1_2_25_1_9561 30 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 89 170 (Polychromatic418967fa.accept_13_3_11_1_1_2122 29 89 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 170 (accept_3_2 28 89 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 89 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 89 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 170
  (Polychromatic418967fa.accept_20_6_9_10_1_8024 26 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 89 170 (accept_3_2 25 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 170 (accept_3_2 22 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 170
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 170 (accept_3_2 19 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 170 (accept_3_2 16 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 89 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 170
  (Polychromatic418967fa.accept_19_14_13_18_1_2680 14 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 89 170 (accept_3_2 13 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 89 170 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 89 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 89 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 170 (accept_3_2 10 89 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 170
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 170 (accept_3_2 7 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  170 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 89 170 (Polychromatic418967fa.accept_18_5_17_8_1_2984 5 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 170 (accept_3_2 4 89 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 89 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 170
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 89 170 (accept_3_2 1 89 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89
  170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 88 170 (Eq.refl
  Bool.true) (allA_of_3_0 83 88 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 87 170 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 87 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 87 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 170 (accept_3_2 82 87 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 87 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 87 170 (Polychromatic418967fa.accept_13_2_9_1_1_67 80
  87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 170 (accept_3_2 79 87
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 87 170 (Polychromatic418967fa.accept_7_1_3_2_1_13
  78 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 87 170 (accept_3_2 76 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  87 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 87 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 170 (accept_3_2 73 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 87 170 (Polychromatic418967fa.accept_11_6_10_5_1_341 72 87 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 87 170 (accept_3_2 70 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  87 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 87 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 170 (accept_3_2 67 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 87 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 87 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 170 (accept_3_2 64 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  87 170 (Polychromatic418967fa.accept_13_11_9_1_1_1407 63 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 87 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 170 (accept_3_2 61 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 87 170 (Polychromatic418967fa.accept_13_8_9_1_1_2147 60 87 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 87 170 (accept_3_2 58 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  87 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 87 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 170 (accept_3_2 55 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 87 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 87 170 (accept_3_2 52 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  87 170 (Polychromatic418967fa.accept_15_6_12_5_1_2108 51 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 87 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 170 (accept_3_2 49 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 87 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 170 (accept_3_2 46 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  87 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 87 170 (Polychromatic418967fa.accept_13_5_9_1_1_1405 44 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 170 (accept_3_2 43 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 87 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 87 170 (accept_3_2 40 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  87 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 87 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 170 (accept_3_2 37 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 87 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 170 (accept_3_2 34 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  87 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 87 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 170 (accept_3_2 31 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 87 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 170 (accept_3_2 28 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 170 (accept_3_2 25 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 170 (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 87 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 170 (accept_3_2 22 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 170 (accept_3_2 19 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 87 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 170 (accept_3_2 16 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 170 (accept_3_2 13 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 87 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 170 (accept_3_2 10 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 87 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 170 (accept_3_2 7 87 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 87 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 87 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 170 (accept_3_2 4 87 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 170
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 170 (accept_3_2 1 87 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 86 170 (Eq.refl
  Bool.true) (allA_succ_of_gcd 84 86 170 2 42 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 86 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 86 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 86 170 2 41 43 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 86 170
  (Polychromatic418967fa.accept_15_6_11_5_1_168 81 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 86 170 2 40 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 86 170 (accept_3_2 79 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86
  170 2 39 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77
  86 170 (Polychromatic418967fa.accept_13_12_8_1_1_825 77 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 86 170 2 38 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 86 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 86 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 170 2 37 43 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 170 (accept_3_2 73 86 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 170 2 36 43 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 170
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 71 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 86 170 2 35 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 86 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 86 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 86 170 2 34 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 86 170 (accept_3_2 67 86 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 86 170 2 33 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 86 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 86 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 86 170 2 32 43 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 86 170
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 63 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 86 170 2 31 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 86 170 (accept_3_2 61 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 86
  170 2 30 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  86 170 (Polychromatic418967fa.accept_13_7_8_1_1_2145 59 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 86 170 2 29 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 86 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 86 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 86 170 2 28 43 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 86 170 (accept_3_2 55 86 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 86 170 2 27 43 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 86 170
  (Polychromatic418967fa.accept_15_8_11_5_1_169 53 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 86 170 2 26 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 86 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 86 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 86 170 2 25 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 86 170 (accept_3_2 49 86 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 86 170 2 24 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 86 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 86 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 86 170 2 23 43 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 86 170
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 86 170 2 22 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 86 170 (accept_3_2 43 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 86
  170 2 21 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  86 170 (Polychromatic418967fa.accept_18_5_14_8_1_2966 41 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 86 170 2 20 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 86 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 86 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 86 170 2 19 43 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 86 170 (accept_3_2 37 86 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86 170 2 18 43 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 86 170
  (Polychromatic418967fa.accept_13_9_8_1_1_824 35 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 86 170 2 17 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 86 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 86 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 86 170 2 16 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 86 170 (accept_3_2 31 86 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86 170 2 15 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 86 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 86 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 170 2 14 43 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 170
  (Polychromatic418967fa.accept_19_8_10_18_1_5232 27 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 170 2 13 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 86 170 (accept_3_2 25 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86
  170 2 12 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  86 170 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 86 170 2 11 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 86 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 86 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 170 2 10 43 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 170 (accept_3_2 19 86 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 170 2 9 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 86 170 (Polychromatic418967fa.accept_15_2_11_5_1_1266
  17 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 170 2 8 43 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 170
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 170 2 7 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 170 (accept_3_2 13 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  170 2 6 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 170 2 5 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 170 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 86 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 170 2 4 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 170 (accept_3_2 7 86 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 170 2 3 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 170 (Polychromatic418967fa.accept_13_5_8_1_1_2161 5 86 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 170 2 2 43 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 170
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 170 2 1 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 170 (accept_3_2 1 86 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 170
  (allA_of_3_0 85 85 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 170 (allA_succ_of_accept 83 84 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 84 170 2 41 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 81 84 170 (Polychromatic418967fa.accept_13_3_6_1_1_3797 81 84 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 84 170 2 40 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 170 (accept_3_2 79 84 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 170 2 39 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 170 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 84 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 170 2 38 42 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 170
  (Polychromatic418967fa.accept_11_9_7_5_1_749 75 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 170 2 37 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 84 170 (accept_3_2 73 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84
  170 2 36 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71
  84 170 (Polychromatic418967fa.accept_15_11_9_5_1_2974 71 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 84 170 2 35 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 84 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 84 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 170 2 34 42 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 170 (accept_3_2 67 84 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 170 2 33 42 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 170 2 32 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 84 170 (Polychromatic418967fa.accept_15_3_9_5_1_2082 63 84 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 170 2 31 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 170 (accept_3_2 61 84 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 170 2 30 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 170 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 84 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 170 2 29 42 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 170
  (Polychromatic418967fa.accept_13_5_6_1_1_822 57 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 84 170 2 28 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 84 170 (accept_3_2 55 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84
  170 2 27 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  84 170 (Polychromatic418967fa.accept_11_9_7_5_1_749 53 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 84 170 2 26 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 84 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 84 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 170 2 25 42 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 170 (accept_3_2 49 84 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 170 2 24 42 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 170 2 23 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 84 170 (Polychromatic418967fa.accept_19_7_8_18_1_1576 45 84 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 170 2 22 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 170 (accept_3_2 43 84 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 170 2 21 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 170 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 84 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 170 2 20 42 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 170
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 39 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 84 170 2 19 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 84 170 (accept_3_2 37 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84
  170 2 18 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  84 170 (Polychromatic418967fa.accept_13_9_6_1_1_2902 35 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 84 170 2 17 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 84 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 84 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 170 2 16 42 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 170 (accept_3_2 31 84 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 170 2 15 42 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 170 2 14 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 84 170 (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 84 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 170 2 13 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 170 (accept_3_2 25 84 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 170 2 12 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 170 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 84 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 170 2 11 42 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 170
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 170 2 10 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 170 (accept_3_2 19 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84
  170 2 9 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  84 170 (Polychromatic418967fa.accept_22_17_18_16_1_9560 17 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 84 170 2 8 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 84 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 84 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 170 2 7 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 170 (accept_3_2 13 84 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 170 2 6 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 84 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 84 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 170 2 5 42 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 170
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 170 2 4 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 170 (accept_3_2 7 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 170
  2 3 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84
  170 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 84 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 170 2 2 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 84 170 (Polychromatic418967fa.accept_13_3_6_1_1_3797 3 84 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 170 2 1 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 170 (accept_3_2 1 84 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 83 170 (allA_succ_of_accept 82 83 170 (accept_3_2 82 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 83 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 83 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 83 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 83 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 170 (accept_3_2 79 83 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 78
  83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 170 (accept_3_2 76 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 83 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 170 (accept_3_2 73 83 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 170 (Polychromatic418967fa.accept_15_12_8_5_1_5048 72 83 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 170
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 170 (accept_3_2 70 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 83 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 170 (accept_3_2 67 83 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 83 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 170 (accept_3_2 64 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 170 (Polychromatic418967fa.accept_20_2_3_10_1_5075 62 83 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 170 (accept_3_2 61 83 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 83 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 170
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 170 (accept_3_2 58 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 170 (Polychromatic418967fa.accept_11_1_6_5_1_1732 56 83 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 170 (accept_3_2 55 83 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 170 (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 83 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 170 (accept_3_2 52 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 83 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 170 (accept_3_2 49 83 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 83 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 170
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 47 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 170 (accept_3_2 46 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 170 (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 83 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 170 (accept_3_2 43 83 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 83 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 170 (accept_3_2 40 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 83 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 170 (accept_3_2 37 83 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 83 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 170
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 35 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 170 (accept_3_2 34 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 83 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 170 (accept_3_2 31 83 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 83 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 170 (accept_3_2 28 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 170 (Polychromatic418967fa.accept_15_11_8_5_1_1278 26 83 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 170 (accept_3_2 25 83 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 83 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 170
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 170 (accept_3_2 22 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 170 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 83 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 170 (accept_3_2 19 83 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 83 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 170 (accept_3_2 16 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 83 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 170 (accept_3_2 13 83 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 83 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 170
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 170 (accept_3_2 10 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 83 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 83 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 170 (accept_3_2 7 83 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 83 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 83 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 170 (accept_3_2 4 83 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 170
  (Polychromatic418967fa.accept_20_2_3_10_1_5075 2 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 170 (accept_3_2 1 83 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 170 (allA_of_3_0
  82 82 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 170 (allA_succ_of_accept 80 81 170
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 80 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 81 170 (accept_3_2 79 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  81 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 78 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 81 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 170 (accept_3_2 76 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 81 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 81 170
  (Polychromatic418967fa.accept_15_14_6_5_1_7215 74 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 81 170 (accept_3_2 73 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  81 170 (Polychromatic418967fa.accept_13_7_3_1_1_814 72 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 81 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 170 (accept_3_2 70 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 81 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 170
  (Polychromatic418967fa.accept_7_5_4_2_1_235 68 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 170 (accept_3_2 67 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  81 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 66 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 81 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 170 (accept_3_2 64 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 81 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 170
  (Polychromatic418967fa.accept_7_6_4_2_1_236 62 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 81 170 (accept_3_2 61 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  81 170 (Polychromatic418967fa.accept_18_6_9_8_1_6812 60 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 81 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 170 (accept_3_2 58 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 170 (Polychromatic418967fa.accept_13_5_3_1_1_1398 57 81 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 170
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 56 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 170 (accept_3_2 55 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  81 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 81 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 170 (accept_3_2 52 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 81 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 170
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 50 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 170 (accept_3_2 49 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  81 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 81 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 170 (accept_3_2 46 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 170 (Polychromatic418967fa.accept_13_6_3_1_1_1413 45 81 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 170
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 44 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 170 (accept_3_2 43 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 170 (accept_3_2 40 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 170
  (Polychromatic418967fa.accept_25_13_6_20_1_9559 38 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 170 (accept_3_2 37 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 170 (Polychromatic418967fa.accept_19_17_5_18_1_6646 36 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 170 (accept_3_2 34 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 81 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 170
  (Polychromatic418967fa.accept_11_10_4_5_1_359 32 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 170 (accept_3_2 31 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 170 (accept_3_2 28 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 170
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 170 (accept_3_2 25 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 170 (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 170 (accept_3_2 22 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 170 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 81 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 170
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 170 (accept_3_2 19 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 170 (accept_3_2 16 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 170
  (Polychromatic418967fa.accept_15_14_6_5_1_7215 14 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 170 (accept_3_2 13 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 170 (accept_3_2 10 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 170 (Polychromatic418967fa.accept_14_9_11_2_1_2501 9 81 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 170
  (Polychromatic418967fa.accept_25_8_6_20_1_9558 8 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 170 (accept_3_2 7 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  170 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 170 (accept_3_2 4 81 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 170 (Polychromatic418967fa.accept_13_2_3_1_1_3823 2
  81 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 170 (accept_3_2 1 81 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 170
  (allA_succ_of_accept 79 80 170 (accept_3_2 79 80 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 80
  170 2 39 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77
  80 170 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 80 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 80 170 2 38 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 75 80 170 5 15 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 80 170 2 37 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 80 170 (accept_3_2 73 80 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 80 170 2 36 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 80 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 80 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 80 170 10 7 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 80 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 80 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 170 2 34 40 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 170 (accept_3_2 67
  80 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 170 2 33 40 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 80 170 5 13 16 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 80 170 2 32 40 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 80 170
  (Polychromatic418967fa.accept_11_8_3_5_1_355 63 80 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 80 170 2 31 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 80 170 (accept_3_2 61 80 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80
  170 10 6 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  80 170 (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 80 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 80 170 2 29 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 80 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 80 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 80 170 2 28 40 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 80 170 5 11 16 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 80 170 2 27 40 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 80 170
  (Polychromatic418967fa.accept_12_5_8_2_1_309 53 80 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 80 170 2 26 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 80 170 (Polychromatic418967fa.accept_13_12_2_1_1_2909 51 80 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 170 10 5 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 170 (accept_3_2 49 80 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 80 170 2 24 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 80 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 80 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 170 2 23 40 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 80 170 5 9 16 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 80 170 2 22 40 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 80 170 (accept_3_2 43 80 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80 170 2 21 40 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 80 170
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 80 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 80 170 10 4 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 80 170 (Polychromatic418967fa.accept_24_15_8_2_1_9557 39 80 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 170 2 19 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 170 (accept_3_2 37 80 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 170 2 18 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 80 170 5 7 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 80 170 2 17 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 80 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 80 170 2 16 40 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 80 170 (accept_3_2 31
  80 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 170 10 3 8 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 170
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 80 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 80 170 2 14 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 80 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 80 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 170 2 13 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 80 170 5 5 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 80 170 2 12 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 170 (Polychromatic418967fa.accept_12_11_8_2_1_1274
  23 80 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 170 2 11 40 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 170
  (Polychromatic418967fa.accept_19_2_4_18_1_9556 21 80 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 170 10 2 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 170 (accept_3_2 19 80 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  170 2 9 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 170 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 80 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 170 2 8 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 80 170 5 3 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 80 170 2 7 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 80 170 (accept_3_2 13 80 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 80 170 2 6 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 80 170 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 80 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 170 10 1 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 170 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 80 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 170 2 4 40 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 170 (accept_3_2 7 80 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 170 2 3 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 80 170 5 1 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 80 170 2 2 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 170 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3
  80 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 170 2 1 40 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 170 (accept_3_2 1 80
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 170 (allA_of_3_0 79
  79 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 170 (allA_succ_of_accept 77 78 170
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 78 170 2 38 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 78 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 78 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 170 2 37 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 170 (accept_3_2 73 78 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 170 2 36 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 170 (Polychromatic418967fa.accept_14_1_8_2_1_1675 71 78 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 170 2 35 39 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 170
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 170 2 34 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 78 170 (accept_3_2 67 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78
  170 2 33 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  78 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 78 170 2 32 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 78 170 (Polychromatic418967fa.accept_12_3_6_2_1_747 63 78 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 78 170 2 31 39 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 170 (accept_3_2 61 78 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 78 170 2 30 39 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 78 170
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 78 170 2 29 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 78 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 78 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 78 170 2 28 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 170 (accept_3_2 55 78 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 170 2 27 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 170 (Polychromatic418967fa.accept_15_8_3_5_1_608 53 78 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 170 2 26 39 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 170
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 170 2 25 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 78 170 (accept_3_2 49 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78
  170 2 24 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  78 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 78 170 2 23 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 78 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 78 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 170 2 22 39 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 170 (accept_3_2 43 78 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 170 2 21 39 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 170
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 78 170 2 20 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 78 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 78 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 170 2 19 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 170 (accept_3_2 37 78 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 170 2 18 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 170 (Polychromatic418967fa.accept_19_16_2_18_1_8136 35 78
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 170 2 17 39 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 170
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 170 2 16 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 78 170 (accept_3_2 31 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78
  170 2 15 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  78 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 78 170 2 14 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 78 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 78 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 170 2 13 39 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 170 (accept_3_2 25 78 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 170 2 12 39 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 170
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 78 170 2 11 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 78 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 78 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 170 2 10 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 170 (accept_3_2 19 78 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 170 2 9 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 78 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 78 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 170 2 8 39 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 170
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 78 170 2 7 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 78 170 (accept_3_2 13 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78
  170 2 6 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  78 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 78 170 2 5 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 78 170 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 78 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 170 2 4 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 170 (accept_3_2 7 78 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 170 2 3 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 78 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 78 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 170 2 2 39 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 170
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 78 170 2 1 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 170 (accept_3_2 1 78 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 170
  (allA_succ_of_accept 76 77 170 (accept_3_2 76 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 77 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 170 (accept_3_2 73 77 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 170 (Polychromatic418967fa.accept_15_12_2_5_1_3939 72 77 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 170 (accept_3_2 70 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 170 (Polychromatic418967fa.accept_12_8_5_2_1_746 68 77 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 170 (accept_3_2 67 77 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 77 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 170
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 170 (accept_3_2 64 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 170 (Polychromatic418967fa.accept_16_14_13_10_1_2624 62 77 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 170 (accept_3_2 61 77 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 77 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 170 (accept_3_2 58 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 77 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 170 (accept_3_2 55 77 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 170 (Polychromatic418967fa.accept_13_2_12_1_1_343 54 77 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 170
  (Polychromatic418967fa.accept_16_5_13_10_1_3664 53 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 170 (accept_3_2 52 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 170 (Polychromatic418967fa.accept_13_11_12_1_1_2154 50 77 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 170 (accept_3_2 49 77 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 77 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 170 (accept_3_2 46 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 170 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 77 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 170 (accept_3_2 43 77 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 77 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 170
  (Polychromatic418967fa.accept_13_2_12_1_1_343 41 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 170 (accept_3_2 40 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 77 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 170 (accept_3_2 37 77 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 170 (Polychromatic418967fa.accept_19_17_1_18_1_2693 36 77 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 170 (accept_3_2 34 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 170 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 77 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 170 (accept_3_2 31 77 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 77 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 170
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 170 (accept_3_2 28 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 170 (Polychromatic418967fa.accept_14_12_7_2_1_1663 26 77 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 170 (accept_3_2 25 77 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 170 (accept_3_2 22 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 77 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 170 (accept_3_2 19 77 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 170 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 77 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 170
  (Polychromatic418967fa.accept_18_17_5_8_1_1898 17 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 170 (accept_3_2 16 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 170 (Polychromatic418967fa.accept_15_14_2_5_1_1272 14 77 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 170 (accept_3_2 13 77 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 77 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 170 (accept_3_2 10 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 170 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 77 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 170 (accept_3_2 7 77 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 77 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 170
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 5 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 170 (accept_3_2 4 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 77 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 170 (accept_3_2 1 77 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 170 (allA_of_3_0 76 76 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 170 (allA_succ_of_accept 74 75
  170 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 170 (accept_3_2 73 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 170 (Polychromatic418967fa.accept_20_12_15_10_1_6520 72 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 75 170 5 14 15 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 75 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 75 170 (Polychromatic418967fa.accept_9_5_3_8_1_316 68 75 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 170 (accept_3_2 67 75 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 75 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 75 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 75 170 5 13 15 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 75 170 (accept_3_2 64 75 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 170 (Polychromatic418967fa.accept_13_11_10_1_1_1409 63 75
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 170
  (Polychromatic418967fa.accept_11_7_9_5_1_338 62 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 170 (accept_3_2 61 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75
  170 5 12 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  75 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 75 170 (accept_3_2 58 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 75 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 75 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 75 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 75 170 5 11 15 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 75 170
  (Polychromatic418967fa.accept_12_6_3_2_1_743 54 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 75 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 170 (accept_3_2 52 75 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 75 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 75 170 5 10 15 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 75 170 (accept_3_2 49 75 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 170 (Polychromatic418967fa.accept_13_9_10_1_1_1389 48 75
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 170 (accept_3_2 46 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75
  170 5 9 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  75 170 (Polychromatic418967fa.accept_16_12_11_10_1_1667 44 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 75 170 (accept_3_2 43 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 75 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 75 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 75 170 5 8 15 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 75 170
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 75 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 170 (accept_3_2 37 75 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 170 (Polychromatic418967fa.accept_20_16_15_10_1_6496 36 75 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 75 170 5 7 15 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 75 170 (accept_3_2 34 75 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 170
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 170 (accept_3_2 31 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75
  170 5 6 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  75 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 75 170 (accept_3_2 28 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 75 170 (Polychromatic418967fa.accept_18_9_3_8_1_5419 27 75 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 170 (Polychromatic418967fa.accept_20_6_15_10_1_3555 26 75
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 75 170 5 5 15 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 75 170
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 170 (accept_3_2 22 75 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 75 170 5 4 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 170 (accept_3_2 19 75 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 75 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 170 (accept_3_2 16 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75
  170 5 3 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  75 170 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 75 170 (accept_3_2 13 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 170 (Polychromatic418967fa.accept_16_12_11_10_1_1667 12 75 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 170 5 2 15 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 75 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 170 (Polychromatic418967fa.accept_20_8_15_10_1_8045 8 75 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 170 (accept_3_2 7 75 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 75 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 75 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 75 170 5 1 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 170 (accept_3_2 4 75 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 75 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 170 (accept_3_2 1 75 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 170 (allA_succ_of_accept
  73 74 170 (accept_3_2 73 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 170 2 36 37 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 170
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 71 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 170 2 35 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 74 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 74 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 170 2 34 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 170 (accept_3_2 67 74 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 170 2 33 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 170 (Polychromatic418967fa.accept_14_9_4_2_1_983 65 74 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 170 2 32 37 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 170
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 63 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 170 2 31 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 74 170 (accept_3_2 61 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 74
  170 2 30 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  74 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 74 170 2 29 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 74 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 74 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 74 170 2 28 37 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 74 170 (accept_3_2 55 74 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 74 170 2 27 37 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 74 170
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 53 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 74 170 2 26 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 74 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 74 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 74 170 2 25 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 74 170 (accept_3_2 49 74 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74 170 2 24 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 74 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 74 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 170 2 23 37 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 170
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 45 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 170 2 22 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 74 170 (accept_3_2 43 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74
  170 2 21 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  74 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 74 170 2 20 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 74 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 74 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 74 170 2 19 37 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 74 170 (accept_3_2 37 74 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74 170 2 18 37 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 74 170
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 35 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 74 170 2 17 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 74 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 74 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 170 2 16 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 170 (accept_3_2 31 74 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 170 2 15 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 170 (Polychromatic418967fa.accept_19_10_17_18_1_9555 29 74
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 170 2 14 37 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 170
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 170 2 13 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 74 170 (accept_3_2 25 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74
  170 2 12 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  74 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 74 170 2 11 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 74 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 74 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 170 2 10 37 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 170 (accept_3_2 19 74 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 170 2 9 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 74 170 (Polychromatic418967fa.accept_15_2_14_5_1_2072
  17 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 170 2 8 37 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 170
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 170 2 7 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 170 (accept_3_2 13 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74
  170 2 6 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  74 170 (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 170 2 5 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 170 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 74 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 170 2 4 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 170 (accept_3_2 7 74 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 170 2 3 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 74 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 74 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 170 2 2 37 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 170
  (Polychromatic418967fa.accept_9_3_2_8_1_108 3 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 170 2 1 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 170 (accept_3_2 1 74 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 170 (allA_of_3_0 73 73 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 170 (allA_succ_of_accept 71 72 170
  (Polychromatic418967fa.accept_13_6_7_1_1_335 71 72 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 72 170 2 35 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 72 170 (Polychromatic418967fa.accept_15_9_12_5_1_1267 69 72 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 170 2 34 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 170 (accept_3_2 67 72 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 170 2 33 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 170 (Polychromatic418967fa.accept_11_10_6_5_1_1239 65 72 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 170 2 32 36 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 170
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 63 72 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 72 170 2 31 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 72 170 (accept_3_2 61 72 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72
  170 2 30 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  72 170 (Polychromatic418967fa.accept_19_2_15_18_1_1556 59 72 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 72 170 2 29 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 72 170 (Polychromatic418967fa.accept_21_15_9_2_1_7973 57 72 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 170 2 28 36 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 170 (accept_3_2 55 72 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 170 2 27 36 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 170
  (Polychromatic418967fa.accept_15_8_12_5_1_2987 53 72 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 72 170 2 26 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 72 170 (Polychromatic418967fa.accept_15_6_12_5_1_2108 51 72 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 170 2 25 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 170 (accept_3_2 49 72 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 170 2 24 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 170 (Polychromatic418967fa.accept_13_8_7_1_1_1385 47 72 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 170 2 23 36 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 170
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 72 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 170 2 22 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 170 (accept_3_2 43 72 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72
  170 2 21 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  72 170 (Polychromatic418967fa.accept_19_3_15_18_1_2682 41 72 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 72 170 2 20 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 72 170 (Polychromatic418967fa.accept_15_9_12_5_1_1267 39 72 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 170 2 19 36 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 170 (accept_3_2 37 72 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 170 2 18 36 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 170
  (Polychromatic418967fa.accept_19_16_15_18_1_5252 35 72 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 72 170 2 17 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 72 170 (Polychromatic418967fa.accept_19_14_15_18_1_5250 33 72 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 72 170 2 16 36 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 170 (accept_3_2 31 72 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 170 2 15 36 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 170
  (Polychromatic418967fa.accept_13_3_7_1_1_334 29 72 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 72 170 2 14 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 72 170 (Polychromatic418967fa.accept_21_6_9_2_1_9554 27 72 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 170 2 13 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 170 (accept_3_2 25 72 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 170 2 12 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 170 (Polychromatic418967fa.accept_11_1_6_5_1_1732 23 72 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 170 2 11 36 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 170
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 72 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 170 2 10 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 170 (accept_3_2 19 72 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  170 2 9 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 170 (Polychromatic418967fa.accept_15_2_12_5_1_2107 17 72 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 170 2 8 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 170 (Polychromatic418967fa.accept_20_15_12_10_1_1291 15 72 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 170 2 7 36 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 170 (accept_3_2 13 72 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 170 2 6 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 170 (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 72 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 170 2 5 36 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 170
  (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 72 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 170 2 4 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 170 (accept_3_2 7 72 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 170
  2 3 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  170 (Polychromatic418967fa.accept_20_5_12_10_1_5072 5 72 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 72 170 2 2 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 72 170 (Polychromatic418967fa.accept_13_3_7_1_1_334 3 72 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 170 2 1 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 170 (accept_3_2 1 72 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 71 170 (allA_succ_of_accept 70 71 170 (accept_3_2 70 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 71 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 71 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 71 170 (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 71
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 170 (accept_3_2 67 71 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 66
  71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 170 (accept_3_2 64 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 71 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 170 (accept_3_2 61 71 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 170 (Polychromatic418967fa.accept_13_8_6_1_1_3808 60 71 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 170
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 170 (accept_3_2 58 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 170 (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 71 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 170 (accept_3_2 55 71 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 170 (Polychromatic418967fa.accept_13_2_6_1_1_3807 54 71 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 170 (accept_3_2 52 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 170 (Polychromatic418967fa.accept_14_8_1_2_1_965 50 71 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 170 (accept_3_2 49 71 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 71 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 170
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 47 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 170 (accept_3_2 46 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 170 (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 71 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 170 (accept_3_2 43 71 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 170 (Polychromatic418967fa.accept_13_3_6_1_1_3797 42 71 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 170 (accept_3_2 40 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 71 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 170 (accept_3_2 37 71 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 170 (Polychromatic418967fa.accept_14_8_1_2_1_965 36 71 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 170
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 35 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 170 (accept_3_2 34 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 170 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 71 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 170 (accept_3_2 31 71 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 170 (Polychromatic418967fa.accept_16_14_7_10_1_898 30 71
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 170 (accept_3_2 28 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 170 (Polychromatic418967fa.accept_19_7_14_18_1_6654 26 71 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 170 (accept_3_2 25 71 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 71 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 170
  (Polychromatic418967fa.accept_15_8_11_5_1_169 23 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 170 (accept_3_2 22 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 71 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 170 (accept_3_2 19 71 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 170 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 71 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 170 (accept_3_2 16 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 170 (Polychromatic418967fa.accept_16_14_7_10_1_898 14 71 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 170 (accept_3_2 13 71 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 170 (Polychromatic418967fa.accept_22_12_5_16_1_9553 12 71
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 170
  (Polychromatic418967fa.accept_22_11_5_16_1_6222 11 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 170 (accept_3_2 10 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 71 170 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 71 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 170 (accept_3_2 7 71 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 71 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 71 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 170 (accept_3_2 4 71 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 170
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 71 170 (accept_3_2 1 71 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 170 (allA_of_3_0 70 70 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 170 (allA_succ_of_accept 68 69 170
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 170 (accept_3_2 67 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 170 (accept_3_2 64 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 69 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 170
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 62 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 170 (accept_3_2 61 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 170 (accept_3_2 58 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 69 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 170
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 170 (accept_3_2 55 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 170 (accept_3_2 52 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 69 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 170
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 170 (accept_3_2 49 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 170 (accept_3_2 46 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 69 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 170
  (Polychromatic418967fa.accept_13_5_4_1_1_364 44 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 170 (accept_3_2 43 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 170 (accept_3_2 40 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 170
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 170 (accept_3_2 37 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 170 (accept_3_2 34 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 170 (Polychromatic418967fa.accept_15_3_9_5_1_2082 33 69 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 170
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 170 (accept_3_2 31 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 170 (accept_3_2 28 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 170
  (Polychromatic418967fa.accept_15_11_9_5_1_2974 26 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 170 (accept_3_2 25 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 170 (accept_3_2 22 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 170
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 170 (accept_3_2 19 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 170 (accept_3_2 16 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 170
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 170 (accept_3_2 13 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 170 (accept_3_2 10 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 170 (Polychromatic418967fa.accept_19_9_12_18_1_8099 9 69 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 170
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 170 (accept_3_2 7 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  170 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 170 (accept_3_2 4 69 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  69 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 170 (accept_3_2 1 69 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 170 (allA_succ_of_accept 67 68
  170 (accept_3_2 67 68 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 170 2 33 34 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 170
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 68 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 170 2 32 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 68 170 (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 68 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 170 2 31 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 170 (accept_3_2 61 68 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 170 2 30 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 68 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 170 2 29 34 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 170
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 68 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 170 2 28 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 170 (accept_3_2 55 68 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68
  170 2 27 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  68 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 68 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 68 170 2 26 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 51 68 170 17 3 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 68 170 2 25 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 68 170 (accept_3_2 49 68 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 68 170 2 24 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 68 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 68 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 68 170 2 23 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 68 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 45
  68 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 170 2 22 34 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 170 (accept_3_2 43
  68 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 170 2 21 34 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 170
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 41 68 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 68 170 2 20 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 68 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 68 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 170 2 19 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 170 (accept_3_2 37 68 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 170 2 18 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 68 170 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 68 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 170 34 1 2 5 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 170
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 68 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 170 2 16 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 68 170 (accept_3_2 31 68 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68
  170 2 15 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  68 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 68 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 68 170 2 14 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 68 170 (Polychromatic418967fa.accept_15_12_8_5_1_5048 27 68 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 170 2 13 34 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 170 (accept_3_2 25 68 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 170 2 12 34 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 170
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 68 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 68 170 2 11 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 68 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 68 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 170 2 10 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 170 (accept_3_2 19 68 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 170 2 9 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 17 68 170 17 1 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 16 68 170 2 8 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 68 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 68 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 170 2 7 34 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 170 (accept_3_2 13 68 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 170 2 6 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 68 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 170 2 5 34 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 170
  (Polychromatic418967fa.accept_22_9_2_16_1_6152 9 68 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 170 2 4 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 170 (accept_3_2 7 68 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 170
  2 3 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  170 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 68 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 68 170 2 2 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 68 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 68 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 170 2 1 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 170 (accept_3_2 1 68 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 170
  (allA_of_3_0 67 67 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 170 (allA_succ_of_accept 65 66 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 66 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 170 2 32 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 66 170 (Polychromatic418967fa.accept_12_3_6_2_1_747 63 66 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 170 2 31 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 170 (accept_3_2 61 66 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 170 2 30 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 170 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 66 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 170 2 29 33 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 170
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 66 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 170 2 28 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 66 170 (accept_3_2 55 66 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66
  170 2 27 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  66 170 (Polychromatic418967fa.accept_19_15_9_18_1_9552 53 66 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 66 170 2 26 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 66 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 66 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 170 2 25 33 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 170 (accept_3_2 49 66 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 170 2 24 33 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 170
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 66 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 170 2 23 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 66 170 (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 66 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 170 2 22 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 170 (accept_3_2 43 66 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 170 2 21 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 66 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 170 2 20 33 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 170
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 66 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 170 2 19 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 66 170 (accept_3_2 37 66 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66
  170 2 18 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  66 170 (Polychromatic418967fa.accept_19_16_9_18_1_8127 35 66 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 66 170 2 17 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 66 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 66 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 170 2 16 33 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 170 (accept_3_2 31 66 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 170 2 15 33 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 170
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 66 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 170 2 14 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 66 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 66 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 170 2 13 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 170 (accept_3_2 25 66 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 170 2 12 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 170 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 66 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 170 2 11 33 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 170
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 66 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 170 2 10 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 66 170 (accept_3_2 19 66 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66
  170 2 9 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  66 170 (Polychromatic418967fa.accept_21_17_3_2_1_2111 17 66 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 66 170 2 8 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 66 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 66 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 170 2 7 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 170 (accept_3_2 13 66 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 170 2 6 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 66 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 66 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 170 2 5 33 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 170
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 66 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 170 2 4 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 170 (accept_3_2 7 66 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 170
  2 3 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66
  170 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 66 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 66 170 2 2 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 66 170 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 66 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 170 2 1 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 170 (accept_3_2 1 66 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 170
  (allA_succ_of_accept 64 65 170 (accept_3_2 64 65 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 65 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 170 (Polychromatic418967fa.accept_20_2_5_10_1_3535 62 65 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 170 (accept_3_2 61 65 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 65 170 5 12 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 65 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 59
  65 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 170 (accept_3_2 58 65
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 170 (Polychromatic418967fa.accept_6_3_5_2_1_12
  57 65 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 170
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 65 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 65 170 5 11 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 65 170 (Polychromatic418967fa.accept_19_16_8_18_1_8139 54 65 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 170 (Polychromatic418967fa.accept_14_11_9_2_1_6382 53 65
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 170 (accept_3_2 52 65 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  65 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 65 170 5 10 13 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 65 170 (accept_3_2 49
  65 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 170
  (Polychromatic418967fa.accept_9_3_2_8_1_108 48 65 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 65 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 65 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 170 (accept_3_2 46 65 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 65 170 5 9 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 65 170 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 65 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 170 (accept_3_2 43 65 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 65 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 170
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 65 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 65 170 5 8 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 65 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 65 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 170 (Polychromatic418967fa.accept_20_18_5_10_1_3533 38 65
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 170 (accept_3_2 37 65 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 170
  (Polychromatic418967fa.accept_20_16_5_10_1_6487 36 65 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 65 170 5 7 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 65 170 (accept_3_2 34 65 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 65 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 170 (accept_3_2 31 65 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 65 170 5 6 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 65 170 (Polychromatic418967fa.accept_19_10_8_18_1_2669 29 65 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 170 (accept_3_2 28 65 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 170
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 26 65 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 65 170 5 5 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 65 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 65 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 170 (accept_3_2 22 65 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  65 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 65 170 5 4 13 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 65 170 (accept_3_2 19
  65 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 170
  (Polychromatic418967fa.accept_14_4_9_2_1_95 18 65 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 65 170 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 65 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 170 (accept_3_2 16 65 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 65 170 5 3 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 65 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 65 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 170 (accept_3_2 13 65 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 65 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 65 170 5 2 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 65 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 170 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 65 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 170 (accept_3_2 7 65 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  65 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 170 5 1 13 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 170 (accept_3_2 4 65
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 170 (Polychromatic418967fa.accept_4_3_1_2_1_62
  3 65 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 170
  (Polychromatic418967fa.accept_20_2_5_10_1_3535 2 65 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 170 (accept_3_2 1 65 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 170 (allA_of_3_0 64 64 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 170 (allA_succ_of_accept 62 63 170
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 62 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 170 (accept_3_2 61 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 170 (Polychromatic418967fa.accept_13_8_11_1_1_3789 60 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 170 (accept_3_2 58 63 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 63 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 170
  (Polychromatic418967fa.accept_22_12_19_16_1_9551 56 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 63 170 (accept_3_2 55 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 63 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 63 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 63 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 170 (accept_3_2 52 63 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 170
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 51 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 170 (Polychromatic418967fa.accept_19_12_6_18_1_8095 50 63 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 170 (accept_3_2 49 63 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 170 (Polychromatic418967fa.accept_13_9_11_1_1_1375 48 63 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 63 170 (accept_3_2 46 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  63 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 63 170 (Polychromatic418967fa.accept_27_17_9_8_1_9550 44 63 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 170 (accept_3_2 43 63 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 63 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 63 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 170 (accept_3_2 40 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  63 170 (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 63 170 (Polychromatic418967fa.accept_13_12_11_1_1_2920 38 63 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 170 (accept_3_2 37 63 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 170 (Polychromatic418967fa.accept_11_3_8_5_1_336 36 63 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 170 (accept_3_2 34 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  63 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 63 170 (Polychromatic418967fa.accept_15_2_3_5_1_2991 32 63 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 170 (accept_3_2 31 63 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 63 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 63 170 (accept_3_2 28 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  63 170 (Polychromatic418967fa.accept_16_11_15_10_1_3515 27 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 63 170 (Polychromatic418967fa.accept_14_12_7_2_1_1663 26 63 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 170 (accept_3_2 25 63 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 170 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 63 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 170 (accept_3_2 22 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  63 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 63 170 (Polychromatic418967fa.accept_13_7_11_1_1_2903 20 63 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 170 (accept_3_2 19 63 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 63 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 170 (accept_3_2 16 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  63 170 (Polychromatic418967fa.accept_20_15_3_10_1_5066 15 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 63 170 (Polychromatic418967fa.accept_11_3_8_5_1_336 14 63 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 170 (accept_3_2 13 63 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 170 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 63 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 170 (accept_3_2 10 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  63 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 170 (Polychromatic418967fa.accept_13_8_11_1_1_3789 8 63 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 170 (accept_3_2 7 63 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 63 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 63 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 170 (accept_3_2 4 63 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 170 (Polychromatic418967fa.accept_11_3_8_5_1_336 3
  63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 170
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 2 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 170 (accept_3_2 1 63 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 170 (allA_succ_of_accept 61 62 170
  (accept_3_2 61 62 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 170 2 30 31 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 170
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 62 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 170 2 29 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 62 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 62 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 170 2 28 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 170 (accept_3_2 55 62 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 170 2 27 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 62 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 170 2 26 31 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 170
  (Polychromatic418967fa.accept_19_13_5_18_1_8106 51 62 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 170 2 25 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 62 170 (accept_3_2 49 62 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62
  170 2 24 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  62 170 (Polychromatic418967fa.accept_16_15_14_10_1_9549 47 62 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 62 170 2 23 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 62 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 62 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 170 2 22 31 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 170 (accept_3_2 43 62 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 170 2 21 31 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 170
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 41 62 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 62 170 2 20 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 62 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 170 2 19 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 170 (accept_3_2 37 62 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 170 2 18 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 170 (Polychromatic418967fa.accept_13_9_10_1_1_1389 35 62 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 170 2 17 31 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 170
  (Polychromatic418967fa.accept_15_3_2_5_1_2980 33 62 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 170 2 16 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 62 170 (accept_3_2 31 62 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62
  170 2 15 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  62 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 62 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 62 170 2 14 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 62 170 (Polychromatic418967fa.accept_15_12_2_5_1_3939 27 62 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 170 2 13 31 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 170 (accept_3_2 25 62 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 170 2 12 31 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 170
  (Polychromatic418967fa.accept_16_7_14_10_1_3544 23 62 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 170 2 11 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 170 (Polychromatic418967fa.accept_16_5_14_10_1_3644 21 62 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 170 2 10 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 170 (accept_3_2 19 62 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 170 2 9 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 62 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 170 2 8 31 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 170
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 62 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 170 2 7 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 170 (accept_3_2 13 62 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  170 2 6 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 62 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 170 2 5 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 170 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 62 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 170 2 4 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 170 (accept_3_2 7 62 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 170 2 3 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 170 (Polychromatic418967fa.accept_16_5_14_10_1_3644 5 62 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 170 2 2 31 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 170
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 62 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 170 2 1 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 170 (accept_3_2 1 62 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 170 (allA_of_3_0 61 61 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 170 (allA_succ_of_accept 59 60 170
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 60 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 170 2 29 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 60 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 170 2 28 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 60 170 5 11 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 60 170 2 27 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 170 (Polychromatic418967fa.accept_16_5_12_10_1_3508
  53 60 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 170 2 26 30 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 170
  (Polychromatic418967fa.accept_13_12_8_1_1_825 51 60 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 170 10 5 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 170 (accept_3_2 49 60 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60
  170 2 24 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  60 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 60 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 60 170 2 23 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 170 5 9 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 170 2 22 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 60 170 (accept_3_2 43 60 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 170 2 21 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 60 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 170 10 4 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 60 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 170 2 19 30 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 170 (accept_3_2 37
  60 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 170 2 18 30 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 60 170 5 7 12 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 60 170 2 17 30 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 170
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 60 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 170 2 16 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 170 (accept_3_2 31 60 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  170 10 3 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 60 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 170 2 14 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 60 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 60 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 170 2 13 30 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 60 170 5 5 12 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 170 2 12 30 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 170
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 60 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 60 170 2 11 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 60 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 60 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 170 10 2 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 170 (accept_3_2 19 60 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 60 170 2 9 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 60 170 (Polychromatic418967fa.accept_23_17_14_9_1_9548 17 60 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 170 2 8 30 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 170 5 3 12 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 170 2 7 30 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 170 (accept_3_2 13 60 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 170 2 6 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 60 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 170 10 1 6 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 170
  (Polychromatic418967fa.accept_13_9_8_1_1_824 9 60 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 170 2 4 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 170 (accept_3_2 7 60 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 170
  2 3 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 60 170 5
  1 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 60 170 2 2
  30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 170
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 60 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 170 2 1 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 170 (accept_3_2 1 60 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 170 (allA_succ_of_accept 58 59 170
  (accept_3_2 58 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 59 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 170 (accept_3_2 55 59 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 59 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 53
  59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 170 (accept_3_2 52 59
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 170 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 170
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 170 (accept_3_2 49 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 59 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 170 (accept_3_2 46 59 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 59 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 170
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 170 (accept_3_2 43 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 59 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 170 (accept_3_2 40 59 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 170
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 170 (accept_3_2 37 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 170 (Polychromatic418967fa.accept_18_17_5_8_1_1898 35 59 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 170 (accept_3_2 34 59 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 170
  (Polychromatic418967fa.accept_11_10_4_5_1_359 32 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 170 (accept_3_2 31 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 170 (accept_3_2 28 59 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 170
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 170 (accept_3_2 25 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 170 (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 59 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 170 (accept_3_2 22 59 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 170
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 170 (accept_3_2 19 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 170 (Polychromatic418967fa.accept_24_18_11_2_1_9547 18 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 170 (accept_3_2 16 59 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 170
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 170 (accept_3_2 13 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 59 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 170 (accept_3_2 10 59 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 170
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 170 (accept_3_2 7 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  170 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 59 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 170 (accept_3_2 4 59 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 59
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 170 (accept_3_2 1 59 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 58 170 (allA_of_3_0 58 58 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 170
  (allA_succ_of_accept 56 57 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 57 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 170 (accept_3_2 55 57 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 57 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 57 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 53
  57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 170 (accept_3_2 52 57
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 170 (Polychromatic418967fa.accept_4_3_1_2_1_62
  51 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 170
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 170 (accept_3_2 49 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 57 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 170 (accept_3_2 46 57 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 57 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 170
  (Polychromatic418967fa.accept_23_21_11_9_1_6020 44 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 170 (accept_3_2 43 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 170 (accept_3_2 40 57 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 170
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 170 (accept_3_2 37 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 170 (Polychromatic418967fa.accept_14_8_1_2_1_965 36 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 57 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 170 (accept_3_2 34 57 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 57 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 170
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 170 (accept_3_2 31 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 170 (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 170 (accept_3_2 28 57 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 170
  (Polychromatic418967fa.accept_29_26_28_25_1_9546 26 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 57 170 (accept_3_2 25 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 57 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 170 (accept_3_2 22 57 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 170 (Polychromatic418967fa.accept_13_8_5_1_1_1381
  21 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 170
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 170 (accept_3_2 19 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 170 (accept_3_2 16 57 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 170
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 170 (accept_3_2 13 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 170 (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 170 (accept_3_2 10 57 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 170 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 57 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 170
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 8 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 170 (accept_3_2 7 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  170 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 170 (accept_3_2 4 57 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  57 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 170 (accept_3_2 1 57 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 170)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 170 (allA_succ_of_accept 55 56 170 (accept_3_2 55 56 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 170 2 27 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 170 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 56 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 170 2 26 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 51
  56 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 170 2 25 28 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 170 (accept_3_2 49
  56 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 170 2 24 28 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 170
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 56 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 170 2 23 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 170 (Polychromatic418967fa.accept_20_5_16_10_1_3558 45 56 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 170 2 22 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 170 (accept_3_2 43 56 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 170 2 21 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 170 2 20 28 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 170
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 56 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 170 2 19 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 170 (accept_3_2 37 56 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  170 2 18 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  56 170 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 56 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 56 170 2 17 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 56 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 56 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 170 2 16 28 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 170 (accept_3_2 31 56 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 170 2 15 28 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 170
  (Polychromatic418967fa.accept_12_5_8_2_1_309 29 56 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 56 170 2 14 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 56 170 (Polychromatic418967fa.accept_21_6_14_2_1_7980 27 56 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 170 2 13 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 170 (accept_3_2 25 56 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 170 2 12 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 56 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 170 2 11 28 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 170
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 56 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 170 2 10 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 170 (accept_3_2 19 56 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  170 2 9 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 170 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 56 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 170 2 8 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 56 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 170 2 7 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 170 (accept_3_2 13 56 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 170 2 6 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 56 170 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 56 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 170 2 5 28 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 170
  (Polychromatic418967fa.accept_15_9_11_5_1_1283 9 56 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 170 2 4 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 170 (accept_3_2 7 56 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 170
  2 3 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56
  170 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 170 2 2 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 56 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 170 2 1 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 170 (accept_3_2 1 56 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 170)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 170 (allA_of_3_0 55
  55 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 170 (allA_succ_of_accept 53 54 170
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 54 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 170 2 26 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 170 (Polychromatic418967fa.accept_12_3_6_2_1_747 51 54 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 170 2 25 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 170 (accept_3_2 49 54 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 170 2 24 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 170 (Polychromatic418967fa.accept_19_9_16_18_1_3887 47 54
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 170 2 23 27 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 170
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 54 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 170 2 22 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 170 (accept_3_2 43 54 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54
  170 2 21 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  54 170 (Polychromatic418967fa.accept_15_11_9_5_1_2974 41 54 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 54 170 2 20 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 54 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 54 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 170 2 19 27 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 170 (accept_3_2 37 54 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 170 2 18 27 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 170
  (Polychromatic418967fa.accept_13_9_2_1_1_813 35 54 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 170 2 17 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 54 170 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 54 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 170 2 16 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 170 (accept_3_2 31 54 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 170 2 15 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 170 (Polychromatic418967fa.accept_13_3_2_1_1_2907 29 54 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 170 2 14 27 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 170
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 54 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 170 2 13 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 170 (accept_3_2 25 54 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54
  170 2 12 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  54 170 (Polychromatic418967fa.accept_25_23_4_20_1_9545 23 54 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 54 170 2 11 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 54 170 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 54 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 170 2 10 27 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 170 (accept_3_2 19 54 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 170 2 9 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 17
  54 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 170 2 8 27 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 170
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 54 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 54 170 2 7 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 170 (accept_3_2 13 54 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54
  170 2 6 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  54 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 54 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 54 170 2 5 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 54 170 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 54 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 170 2 4 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 170 (accept_3_2 7 54 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 170 2 3 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 54 170 (Polychromatic418967fa.accept_20_5_14_10_1_1269 5 54 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 170 2 2 27 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 170
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 54 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 170 2 1 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 170 (accept_3_2 1 54 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  170)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 170 (allA_succ_of_accept 52 53 170 (accept_3_2
  52 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 170 (Polychromatic418967fa.accept_19_12_15_18_1_9544 50 53 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 170 (accept_3_2 49 53 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 53 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 170 (accept_3_2 46 53
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 170 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 53 170
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 53 170 (accept_3_2 43 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  53 170 (Polychromatic418967fa.accept_15_12_8_5_1_5048 42 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 53 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 53 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 170 (accept_3_2 40 53 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 53 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 170
  (Polychromatic418967fa.accept_18_2_17_8_1_1893 38 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 170 (accept_3_2 37 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 170 (Polychromatic418967fa.accept_25_11_3_20_1_9543 36 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 170 (accept_3_2 34 53 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 170
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 170 (accept_3_2 31 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 170 (Polychromatic418967fa.accept_16_14_5_10_1_3622 30 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 170 (Polychromatic418967fa.accept_11_7_9_5_1_338 29 53 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 170 (accept_3_2 28 53 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 170
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 170 (accept_3_2 25 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 170 (Polychromatic418967fa.accept_22_2_9_16_1_6269 24 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 170 (accept_3_2 22 53 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 170
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 170 (accept_3_2 19 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 170 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 170 (Polychromatic418967fa.accept_20_17_13_10_1_5059 17 53 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 170 (accept_3_2 16 53 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 170
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 170 (accept_3_2 13 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 170 (accept_3_2 10 53 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 170
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 170 (accept_3_2 7 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  170 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 53 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 170 (accept_3_2 4 53 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 170 (Polychromatic418967fa.accept_18_2_17_8_1_1893
  2 53 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 170 (accept_3_2 1 53
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 170)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 52 170 (allA_of_3_0 52 52 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 170
  (allA_succ_of_accept 50 51 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 51 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 170 (accept_3_2 49 51 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 51 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 47
  51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 170 (accept_3_2 46 51
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 170 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 170
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 44 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 170 (accept_3_2 43 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 170 (Polychromatic418967fa.accept_11_9_7_5_1_749 42 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 170 (accept_3_2 40 51 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 51 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 170
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 170 (accept_3_2 37 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 170 (Polychromatic418967fa.accept_19_17_13_18_1_9542 36 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 51 170 17 2 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 51 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 170
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 170 (accept_3_2 31 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 170 (accept_3_2 28 51 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 170 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 51 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 170
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 170 (accept_3_2 25 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 170 (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 170 (accept_3_2 22 51 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 170
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 170 (accept_3_2 19 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 17 51 170 17 1 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 16 51 170 (accept_3_2 16 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 51 170 (Polychromatic418967fa.accept_13_2_12_1_1_343 15 51 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 51 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 170 (accept_3_2 13 51 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 12
  51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 170 (accept_3_2 10 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  51 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 170 (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 51 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 170 (accept_3_2 7 51 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 51 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 51 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 170 (accept_3_2 4 51 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 170
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 170 (accept_3_2 1 51 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  170))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 170 (allA_succ_of_accept 49 50 170 (accept_3_2 49
  50 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50 170 2 24 25 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 50 170
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 50 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 50 170 2 23 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 50 170 5 9 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 50 170 2 22 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 50 170 (accept_3_2 43 50 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50
  170 2 21 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  50 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 50 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 50 170 10 4 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 50 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 50 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 170 2 19 25 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 170 (accept_3_2 37 50 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 170 2 18 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 50 170 5 7 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 50 170 2 17 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 33
  50 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 170 2 16 25 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 170 (accept_3_2 31
  50 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 170 10 3 5 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 170
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 50 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 50 170 2 14 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 50 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 50 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 170 2 13 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 50 170 5 5 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 50 170 2 12 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 170 (Polychromatic418967fa.accept_11_1_6_5_1_1732
  23 50 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 170 2 11 25 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 170
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 50 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 170 10 2 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 50 170 (accept_3_2 19 50 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50
  170 2 9 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  50 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 50 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 50 170 2 8 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 50 170 5 3 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 50 170 2 7 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 50 170 (accept_3_2 13 50 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 50 170 2 6 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 50 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 50 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 170 10 1 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 170 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 50 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 170 2 4 25 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 170 (accept_3_2 7 50 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 170 2 3 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 50 170 5 1 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 50 170 2 2 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 50
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 170 2 1 25 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 170 (accept_3_2 1 50
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 170))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 170 (allA_of_3_0 49 49 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 170
  (allA_succ_of_accept 47 48 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 48 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 170 2 23 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 45
  48 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 170 2 22 24 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 170 (accept_3_2 43
  48 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 170 2 21 24 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 170
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 48 170 2 20 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 48 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 48 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 170 2 19 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 170 (accept_3_2 37 48 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 170 2 18 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 170 (Polychromatic418967fa.accept_20_15_8_10_1_3602 35 48
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 170 2 17 24 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 170
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 48 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 170 2 16 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 170 (accept_3_2 31 48 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48
  170 2 15 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  48 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 48 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 48 170 2 14 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 48 170 (Polychromatic418967fa.accept_19_8_10_18_1_5232 27 48 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 170 2 13 24 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 170 (accept_3_2 25 48 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 170 2 12 24 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 170
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 48 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 48 170 2 11 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 48 170 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 48 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 170 2 10 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 170 (accept_3_2 19 48 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 170 2 9 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 48 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 48 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 170 2 8 24 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48 170
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 48 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 48 170 2 7 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 48 170 (accept_3_2 13 48 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48
  170 2 6 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  48 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 48 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 48 170 2 5 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 48 170 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 48 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 170 2 4 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 170 (accept_3_2 7 48 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 170 2 3 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 48 170 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 48 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 170 2 2 24 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48 170
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 48 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 48 170 2 1 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 48 170 (accept_3_2 1 48 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  170)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 170 (allA_succ_of_accept 46 47 170 (accept_3_2 46 47
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 170 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 170
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 47 170 (accept_3_2 43 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  47 170 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 47 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 47 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 170 (accept_3_2 40 47 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 170
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 170 (accept_3_2 37 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 170 (Polychromatic418967fa.accept_22_14_3_16_1_9541 36 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 170 (Polychromatic418967fa.accept_13_9_8_1_1_824 35 47 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 170 (accept_3_2 34 47 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 170
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 170 (accept_3_2 31 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 170 (accept_3_2 28 47 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 170
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 26 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 170 (accept_3_2 25 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 47 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 170 (accept_3_2 22 47 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 170
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 170 (accept_3_2 19 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 170 (accept_3_2 16 47 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 170
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 170 (accept_3_2 13 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 47 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 170 (accept_3_2 10 47 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 170
  (Polychromatic418967fa.accept_11_8_3_5_1_355 8 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 170 (accept_3_2 7 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  170 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 170 (accept_3_2 4 47 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 170 (Polychromatic418967fa.accept_19_2_9_18_1_6651
  2 47 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 170 (accept_3_2 1 47
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 170)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 46 170 (allA_of_3_0 46 46 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 170
  (allA_succ_of_accept 44 45 170 (Polychromatic418967fa.accept_13_5_6_1_1_822 44 45 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 170 (accept_3_2 43 45 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 45 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 45 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 41
  45 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 170 5 8 9 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 45 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 45 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 45 170 (Polychromatic418967fa.accept_20_18_5_10_1_3533 38 45 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 170 (accept_3_2 37 45 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 45 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 45 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 45 170 5 7 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 170 (accept_3_2 34 45 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 45 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 170
  (Polychromatic418967fa.accept_20_12_5_10_1_9540 32 45 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 170 (accept_3_2 31 45 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45
  170 5 6 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  45 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 45 170 (accept_3_2 28 45 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 45 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 45 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 170 5 5 9 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 45 170
  (Polychromatic418967fa.accept_18_6_9_8_1_6812 24 45 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 170 (accept_3_2 22 45 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 170 (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 45 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 45 170 5 4 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 45 170 (accept_3_2 19 45 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 45 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 170 (accept_3_2 16 45 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45
  170 5 3 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  45 170 (Polychromatic418967fa.accept_16_14_13_10_1_2624 14 45 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 45 170 (accept_3_2 13 45 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 45 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 45 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 45 170 5 2 9 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 45 170
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 45 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 45 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 170 (accept_3_2 7 45 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 45 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 45 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 45 170 5 1 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 170 (accept_3_2 4 45 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 170
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 45 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 45 170 (accept_3_2 1 45 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  170))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 170 (allA_succ_of_accept 43 44 170 (accept_3_2 43 44
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 170 2 21 22 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 170
  (Polychromatic418967fa.accept_12_5_8_2_1_309 41 44 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 44 170 2 20 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 44 170 (Polychromatic418967fa.accept_15_9_14_5_1_2086 39 44 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 170 2 19 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 170 (accept_3_2 37 44 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 170 2 18 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 170 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 44 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 170 2 17 22 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 170
  (Polychromatic418967fa.accept_26_7_18_14_1_9539 33 44 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 170 2 16 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 170 (accept_3_2 31 44 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  170 2 15 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  44 170 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 44 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 170 2 14 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 44 170 (Polychromatic418967fa.accept_16_11_12_10_1_3641 27 44 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 170 2 13 22 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 170 (accept_3_2 25 44 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 170 2 12 22 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 170
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 44 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 44 170 2 11 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 44 170 (Polychromatic418967fa.accept_13_8_5_1_1_1381 21 44 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 170 2 10 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 170 (accept_3_2 19 44 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 170 2 9 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 44 170 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 44 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 170 2 8 22 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 170
  (Polychromatic418967fa.accept_20_15_4_10_1_9538 15 44 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 44 170 2 7 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 44 170 (accept_3_2 13 44 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44
  170 2 6 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  44 170 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 44 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 44 170 2 5 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 44 170 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 44 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 170 2 4 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 170 (accept_3_2 7 44 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 170 2 3 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 44 170 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 44 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 170 2 2 22 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 170
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 44 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 44 170 2 1 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 44 170 (accept_3_2 1 44 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  170)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 170 (allA_of_3_0 43 43 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 42 170 (allA_succ_of_accept 41 42 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 42 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 170 2 20 21 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 170
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 42 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 170 2 19 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 170 (accept_3_2 37 42 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42
  170 2 18 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  42 170 (Polychromatic418967fa.accept_20_15_2_10_1_8052 35 42 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 42 170 2 17 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 42 170 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 42 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 170 2 16 21 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 170 (accept_3_2 31 42 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 170 2 15 21 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 170
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 42 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 170 2 14 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 42 170 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 42 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 170 2 13 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 170 (accept_3_2 25 42 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 170 2 12 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 42 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 170 2 11 21 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 170
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 42 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 170 2 10 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 170 (accept_3_2 19 42 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42
  170 2 9 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  42 170 (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 42 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 170 2 8 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 170 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 42 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 170 2 7 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 170 (accept_3_2 13 42 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 170 2 6 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 42 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 42 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 170 2 5 21 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 170
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 42 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 170 2 4 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 170 (accept_3_2 7 42 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 170
  2 3 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42
  170 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 42 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 42 170 2 2 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 42 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 42 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 170 2 1 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 170 (accept_3_2 1 42 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 170)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 170 (allA_succ_of_accept 40 41
  170 (accept_3_2 40 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 41 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 170 (accept_3_2 37 41 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 41 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  41 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 170 (accept_3_2 34 41
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 170 (Polychromatic418967fa.accept_6_3_5_2_1_12
  33 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 170
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 170 (accept_3_2 31 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 41 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 170 (accept_3_2 28 41 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 170
  (Polychromatic418967fa.accept_21_5_20_2_1_7948 26 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 170 (accept_3_2 25 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 170 (accept_3_2 22 41 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 170
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 170 (accept_3_2 19 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 41 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 170 (accept_3_2 16 41 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 170
  (Polychromatic418967fa.accept_11_3_8_5_1_336 14 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 170 (accept_3_2 13 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 170 (accept_3_2 10 41 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 170
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 170 (accept_3_2 7 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  170 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 41 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 170 (Polychromatic418967fa.accept_20_5_1_10_1_6523 5 41 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 170 (accept_3_2 4 41 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 41
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 170 (accept_3_2 1 41 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 170))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 170
  (allA_of_3_0 40 40 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 170 (allA_succ_of_accept 38 39 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 170 (accept_3_2 37 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 170 (Polychromatic418967fa.accept_19_17_1_18_1_2693 36 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 170 (accept_3_2 34 39 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 170
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 170 (accept_3_2 31 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 170 (accept_3_2 28 39 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 39 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 170
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 170 (accept_3_2 25 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 170 (accept_3_2 22 39 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 170
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 170 (accept_3_2 19 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 170 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 170 (accept_3_2 16 39 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 170 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 39 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 170
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 170 (accept_3_2 13 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 170 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 170 (accept_3_2 10 39 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 170
  (Polychromatic418967fa.accept_19_8_1_18_1_5240 8 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 170 (accept_3_2 7 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  170 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 39 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 170 (accept_3_2 4 39 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 170 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 39 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  39 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 170 (accept_3_2 1 39 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 170))))))))))))))))))))))))))))))))))))))) (allB_succ 38 170
  (allA_succ_of_accept 37 38 170 (accept_3_2 37 38 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  170 2 18 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 170 (Polychromatic418967fa.accept_18_17_2_8_1_6800 35 38 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 170 2 17 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 38 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 170 2 16 19 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 170 (accept_3_2 31 38 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 170 2 15 19 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 170
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 38 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 170 2 14 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 170 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 38 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 170 2 13 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 170 (accept_3_2 25 38 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 170 2 12 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 38 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 170 2 11 19 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 170
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 38 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 170 2 10 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 170 (accept_3_2 19 38 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  170 2 9 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 170 (Polychromatic418967fa.accept_18_17_2_8_1_6800 17 38 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 170 2 8 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 38 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 170 2 7 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 170 (accept_3_2 13 38 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 170 2 6 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 170 (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 38 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 170 2 5 19 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 170
  (Polychromatic418967fa.accept_21_9_17_2_1_9537 9 38 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 170 2 4 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 170 (accept_3_2 7 38 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 170
  2 3 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  170 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 38 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 170 2 2 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 38 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 170 2 1 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 170 (accept_3_2 1 38 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 170)))))))))))))))))))))))))))))))))))))) (allB_succ 37 170 (allA_of_3_0 37 37 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 36 170 (allA_succ_of_accept 35 36 170
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 35 36 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 170 2 17 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 170 (Polychromatic418967fa.accept_15_3_6_5_1_2079 33 36 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 170 2 16 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 170 (accept_3_2 31 36 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 170 2 15 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 170 (Polychromatic418967fa.accept_14_1_8_2_1_1675 29 36 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 170 2 14 18 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 170
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 36 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 170 2 13 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 170 (accept_3_2 25 36 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36
  170 2 12 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  36 170 (Polychromatic418967fa.accept_19_4_17_18_1_9536 23 36 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 36 170 2 11 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 36 170 (Polychromatic418967fa.accept_27_21_9_8_1_9535 21 36 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 170 2 10 18 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 170 (accept_3_2 19 36 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 170 2 9 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 17
  36 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 170 2 8 18 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 170
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 15 36 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 36 170 2 7 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 170 (accept_3_2 13 36 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36
  170 2 6 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  36 170 (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 36 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 36 170 2 5 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 36 170 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 36 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 170 2 4 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 170 (accept_3_2 7 36 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 170 2 3 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 36 170 (Polychromatic418967fa.accept_19_5_17_18_1_2686 5 36 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 170 2 2 18 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 170
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 36 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 170 2 1 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 170 (accept_3_2 1 36 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  170)))))))))))))))))))))))))))))))))))) (allB_succ 35 170 (allA_succ_of_accept 34 35 170 (accept_3_2 34 35 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  35 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 170
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 35 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 170 (accept_3_2 31 35 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 35
  170 5 6 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  35 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 35 170 (accept_3_2 28 35 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 35 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 170 (Polychromatic418967fa.accept_14_12_7_2_1_1663 26 35
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 35 170 5 5 7 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 35 170
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 35 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 35 170 (Polychromatic418967fa.accept_13_10_9_1_1_5609 23 35 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 170 (accept_3_2 22 35 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 35 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 35 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 35 170 5 4 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 35 170 (accept_3_2 19 35 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 170 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 35 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 170 (accept_3_2 16 35 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 35
  170 5 3 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  35 170 (Polychromatic418967fa.accept_19_14_16_18_1_9534 14 35 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 35 170 (accept_3_2 13 35 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 35 170 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 35 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 170 (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 35
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 35 170 5 2 7 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 35 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 170 (Polychromatic418967fa.accept_11_8_2_5_1_1769 8 35 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 170 (accept_3_2 7 35 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 170 (Polychromatic418967fa.accept_13_6_9_1_1_5604 6 35 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 170 5 1 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 170 (accept_3_2 4 35 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 170
  (Polychromatic418967fa.accept_13_2_9_1_1_67 2 35 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 170 (accept_3_2 1 35 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  170))))))))))))))))))))))))))))))))))) (allB_succ 34 170 (allA_of_3_0 34 34 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 170 (allA_succ_of_accept 32 33 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 33 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 170 (accept_3_2 31 33 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 30
  33 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 170 (accept_3_2 28 33 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 170 (Polychromatic418967fa.accept_19_7_14_18_1_6654 26 33 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 170 (accept_3_2 25 33 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 33 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 170 (accept_3_2 22 33 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 33 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 33 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 170 (accept_3_2 19 33 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 33 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 170 (accept_3_2 16 33 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 33 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 170 (accept_3_2 13 33 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 170 (accept_3_2 10 33 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 170 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 33 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 170 (Polychromatic418967fa.accept_13_8_7_1_1_1385 8 33 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 170 (accept_3_2 7 33 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 33 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 170
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 170 (accept_3_2 4 33 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 33 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 170 (accept_3_2 1 33 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 170))))))))))))))))))))))))))))))))) (allB_succ 32 170 (allA_succ_of_accept 31 32 170
  (accept_3_2 31 32 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 170 2 15 16 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 170
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 32 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 170 2 14 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 170 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 32 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 170 2 13 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 170 (accept_3_2 25 32 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 170 2 12 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 170 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 32 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 170 2 11 16 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 170
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 32 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 170 2 10 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 170 (accept_3_2 19 32 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  170 2 9 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 170 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 32 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 170 2 8 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 170 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 32 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 170 2 7 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 170 (accept_3_2 13 32 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 170 2 6 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 170 2 5 16 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 170
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 32 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 170 2 4 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 170 (accept_3_2 7 32 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 170
  2 3 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  170 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 32 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 170 2 2 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 32 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 170 2 1 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 170 (accept_3_2 1 32 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 170)))))))))))))))))))))))))))))))) (allB_succ 31 170 (allA_of_3_0 31 31 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 170 (allA_succ_of_accept 29 30 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 30 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 170 2 14 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 30 170 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 30 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 170 2 13 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 30 170 5 5 6 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 30 170 2 12 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 170 (Polychromatic418967fa.accept_9_5_3_8_1_316 23
  30 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 170 2 11 15 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 170
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 30 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 170 10 2 3 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 170 (accept_3_2 19 30 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30
  170 2 9 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  30 170 (Polychromatic418967fa.accept_19_17_11_18_1_9533 17 30 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 170 2 8 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 30 170 5 3 6 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 30 170 2 7 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 30 170 (accept_3_2 13 30 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 170 2 6 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 30 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 170 10 1 3 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 170 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 30 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 170 2 4 15 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 170 (accept_3_2 7 30 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 170 2 3 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 170 5 1 6 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 30 170 2 2 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 170 (Polychromatic418967fa.accept_11_3_8_5_1_336 3
  30 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 170 2 1 15 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 170 (accept_3_2 1 30
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 170)))))))))))))))))))))))))))))) (allB_succ 29 170
  (allA_succ_of_accept 28 29 170 (accept_3_2 28 29 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  29 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 170 (Polychromatic418967fa.accept_19_7_10_18_1_6695 26 29 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 170 (accept_3_2 25 29 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 29 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 29 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 170 (accept_3_2 22 29 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 29 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 170 (accept_3_2 19 29 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 170 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 29 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 170
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 29 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 170 (accept_3_2 16 29 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 170 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 29 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 170 (accept_3_2 13 29 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 170 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 29 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 170 (accept_3_2 10 29 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 170 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 29 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 170 (accept_3_2 7 29 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 170 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 29 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 170
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 29 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 170 (accept_3_2 4 29 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 170 (Polychromatic418967fa.accept_13_2_3_1_1_3823 2 29 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 170 (accept_3_2 1 29 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 170))))))))))))))))))))))))))))) (allB_succ 28 170 (allA_of_3_0 28 28 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 170 (allA_succ_of_accept 26 27 170 (Polychromatic418967fa.accept_19_7_8_18_1_1576
  26 27 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 170 (accept_3_2 25
  27 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 170
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 27 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 170 (accept_3_2 22 27 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 170 (Polychromatic418967fa.accept_19_1_8_18_1_6667
  20 27 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 170 (accept_3_2 19
  27 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 170
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 27 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 170 (accept_3_2 16 27 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 170 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 27 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 170 (Polychromatic418967fa.accept_21_14_6_2_1_4793
  14 27 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 170 (accept_3_2 13
  27 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 170
  (Polychromatic418967fa.accept_16_12_11_10_1_1667 12 27 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 170 (accept_3_2 10 27 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 170
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 27 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 170 (accept_3_2 7 27 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  170 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 27 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 170 (accept_3_2 4 27 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 27 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 170 (Polychromatic418967fa.accept_15_2_12_5_1_2107
  2 27 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 170 (accept_3_2 1 27
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 170))))))))))))))))))))))))))) (allB_succ 26 170
  (allA_succ_of_accept 25 26 170 (accept_3_2 25 26 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  170 2 12 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 170 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 26 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 170 2 11 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 170 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 26 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 170 2 10 13 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 170 (accept_3_2 19 26 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 170 2 9 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 17
  26 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 170 2 8 13 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 170
  (Polychromatic418967fa.accept_19_15_7_18_1_9532 15 26 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 170 2 7 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 170 (accept_3_2 13 26 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  170 2 6 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 26 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 170 2 5 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 170 (Polychromatic418967fa.accept_15_9_11_5_1_1283 9 26 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 170 2 4 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 170 (accept_3_2 7 26 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 170 2 3 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 170 (Polychromatic418967fa.accept_20_5_6_10_1_3536 5 26 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 170 2 2 13 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 170
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 26 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 170 2 1 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 170 (accept_3_2 1 26 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  170)))))))))))))))))))))))))) (allB_succ 25 170 (allA_of_3_0 25 25 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 170 (allA_succ_of_accept 23 24 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 24 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 170 2 11 12 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 170
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 170 2 10 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 170 (accept_3_2 19 24 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  170 2 9 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 170 (Polychromatic418967fa.accept_19_17_5_18_1_6646 17 24 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 170 2 8 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 170 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 24 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 170 2 7 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 170 (accept_3_2 13 24 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 170 2 6 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 24 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 24 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 170 2 5 12 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 170
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 24 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 170 2 4 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 170 (accept_3_2 7 24 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 170
  2 3 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  170 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 24 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 170 2 2 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 24 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 170 2 1 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 170 (accept_3_2 1 24 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 170)))))))))))))))))))))))) (allB_succ 23 170 (allA_succ_of_accept 22 23 170 (accept_3_2 22
  23 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 170
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 23 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 170 (accept_3_2 19 23 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 170 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 23 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  23 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 170 (accept_3_2 16 23
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 170 (Polychromatic418967fa.accept_6_3_5_2_1_12
  15 23 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 170
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 23 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 170 (accept_3_2 13 23 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 23 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 23 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 170 (accept_3_2 10 23 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 170
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 23 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 170 (accept_3_2 7 23 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  170 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 23 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 170 (accept_3_2 4 23 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 23
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 170 (accept_3_2 1 23 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 170))))))))))))))))))))))) (allB_succ 22 170 (allA_of_3_0 22 22
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 170 (allA_succ_of_accept 20 21 170
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 21 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 170 (accept_3_2 19 21 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 170 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 21 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 170 (accept_3_2 16 21 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 170
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 21 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 170 (accept_3_2 13 21 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 170 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 21 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 170 (accept_3_2 10 21 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 170 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 21 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 170
  (Polychromatic418967fa.accept_25_8_21_20_1_9531 8 21 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 170 (accept_3_2 7 21 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  170 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 21 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 170 (accept_3_2 4 21 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  21 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 170 (accept_3_2 1 21 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 170))))))))))))))))))))) (allB_succ 20 170 (allA_succ_of_accept
  19 20 170 (accept_3_2 19 20 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 170 2 9 10 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 170
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 20 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 170 2 8 10 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 20 170 5 3 4 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 20 170 2 7 10 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 20 170 (accept_3_2 13 20 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20
  170 2 6 10 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  20 170 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 20 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 20 170 10 1 2 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 20 170 (Polychromatic418967fa.accept_21_9_20_2_1_8000 9 20 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 170 2 4 10 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 170 (accept_3_2 7 20 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 170 2 3 10 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 5 20 170 5 1 4 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 4 20 170 2 2 10 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 20 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 20 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 170 2 1 10 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 170 (accept_3_2 1 20 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 20 170)))))))))))))))))))) (allB_succ 19 170 (allA_of_3_0 19 19 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 18 170 (allA_succ_of_accept 17 18 170
  (Polychromatic418967fa.accept_13_4_5_1_1_833 17 18 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 18 170 2 8 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 18 170 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 18 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 18 170 2 7 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 18 170 (accept_3_2 13 18 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 18 170 2 6 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 18 170 (Polychromatic418967fa.accept_22_11_18_16_1_9530 11 18 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 170 2 5 9 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 18 170
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 18 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 18 170 2 4 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 18 170 (accept_3_2 7 18 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 170
  2 3 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 170
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 18 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 18 170 2 2 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 18 170 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 18 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 18 170 2 1 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 170 (accept_3_2 1 18 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 18 170)))))))))))))))))) (allB_succ 17 170 (allA_succ_of_accept 16 17 170 (accept_3_2 16 17 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  17 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 170
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 14 17 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 170 (accept_3_2 13 17 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 17 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 170 (accept_3_2 10 17 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 170 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 170
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 17 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 170 (accept_3_2 7 17 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  170 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 17 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 170 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 17 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 170 (accept_3_2 4 17 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 170 (Polychromatic418967fa.accept_18_2_17_8_1_1893
  2 17 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 170 (accept_3_2 1 17
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 170))))))))))))))))) (allB_succ 16 170 (allA_of_3_0 16 16
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 170 (allA_succ_of_accept 14 15 170
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 15 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 170 (accept_3_2 13 15 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 170 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 15 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 170 5 2 3 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 15 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 170
  (Polychromatic418967fa.accept_14_8_1_2_1_965 8 15 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 170 (accept_3_2 7 15 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  170 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 15 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 15 170 5 1 3 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 15 170 (accept_3_2 4 15 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15
  170 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 15 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 15 170 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 15 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 170 (accept_3_2 1 15 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 15 170))))))))))))))) (allB_succ 14 170 (allA_succ_of_accept 13 14 170 (accept_3_2 13 14 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 170 2 6 7 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 11
  14 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 170 2 5 7 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 170
  (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 14 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 14 170 2 4 7 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 14 170 (accept_3_2 7 14 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 14 170
  2 3 7 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14 170
  (Polychromatic418967fa.accept_16_5_14_10_1_3644 5 14 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 14 170 2 2 7 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 14 170 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 14 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 170 2 1 7 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 170 (accept_3_2 1 14 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 170)))))))))))))) (allB_succ 13 170 (allA_of_3_0 13 13 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 170 (allA_succ_of_accept 11 12 170 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 12 170
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 170 2 5 6 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 170
  (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 12 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 170 2 4 6 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 170 (accept_3_2 7 12 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 170
  2 3 6 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 170
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 12 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 12 170 2 2 6 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 12 170 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 12 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 170 2 1 6 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 170 (accept_3_2 1 12 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 170)))))))))))) (allB_succ 11 170 (allA_succ_of_accept 10 11 170 (accept_3_2 10 11 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 170
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 11 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 170 (accept_3_2 7 11 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  170 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 11 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 170 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 170 (accept_3_2 4 11 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 170 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 170 (Polychromatic418967fa.accept_15_2_11_5_1_1266
  2 11 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 170 (accept_3_2 1 11
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 170))))))))))) (allB_succ 10 170 (allA_of_3_0 10 10 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 170 (allA_succ_of_accept 8 9 170
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 8 9 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 170 (accept_3_2 7 9 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 170
  (Polychromatic418967fa.accept_12_6_9_2_1_311 6 9 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 170 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 170 (accept_3_2 4 9 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 9 170 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 170 (Polychromatic418967fa.accept_13_2_9_1_1_67 2 9
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 170 (accept_3_2 1 9 170
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 170))))))))) (allB_succ 8 170 (allA_succ_of_accept 7 8 170
  (accept_3_2 7 8 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 170 2 3 4 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 170
  (Polychromatic418967fa.accept_12_5_8_2_1_309 5 8 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 8 170 2 2 4 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 8 170 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 8 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 170 2 1 4 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 170 (accept_3_2 1 8 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 170)))))))) (allB_succ 7 170 (allA_of_3_0 7 7 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 6 170 (allA_succ_of_accept 5 6 170 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 6 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 170 2 2 3 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 170 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 6
  170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 6 170 2 1 3 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 170 (accept_3_2 1 6
  170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 170)))))) (allB_succ 5 170 (allA_succ_of_accept 4 5 170
  (accept_3_2 4 5 170 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 170
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 5 170 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 5 170 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 5 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 170 (accept_3_2 1 5 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 5 170))))) (allB_succ 4 170 (allA_of_3_0 4 4 170 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 3 170 (allA_succ_of_accept 2 3 170 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 3 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 170 (accept_3_2 1 3 170 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 3 170))) (allB_succ 2 170 (allA_succ_of_accept 1 2 170 (accept_3_2 1 2 170 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 2 170)) (allB_two
  170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


