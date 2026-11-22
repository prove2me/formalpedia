-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch158
-- name    : Polychromatic418967fa_Branch158
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:17:20.568629+00:00
-- url     : https://prove2.me/theorems/54d71fb2-4d25-4cb9-b974-7f1945cfb9f7
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

def Polychromatic418967fa.branch_158 : allB 158 158 :=
  allB_succ' 2 157 158 (Eq.refl Bool.true) (allA_of_3_0 2 157 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  156 158 (Eq.refl Bool.true) (allA_succ_of_gcd 2 156 158 2 1 78 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 158 (accept_3_2 1 156 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 156 158))) (allB_succ' 4 155 158 (Eq.refl Bool.true) (allA_succ_of_accept 3 155 158
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 155 158 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 155 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 158 (accept_3_2 1 155 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 155 158)))) (allB_succ' 5 154 158 (Eq.refl Bool.true) (allA_of_3_0 5 154 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 153 158 (Eq.refl Bool.true) (allA_succ_of_accept 5 153 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 158 (accept_3_2 4 153 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 153 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 153 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 158 (accept_3_2 1 153 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 153 158)))))) (allB_succ' 7 152 158 (Eq.refl Bool.true) (allA_succ_of_gcd 6 152 158 2 3
  76 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 152 158
  (Polychromatic418967fa.accept_10_5_2_8_1_135 5 152 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 152 158 2 2 76 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 152 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 152 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 158 2 1 76 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 158 (accept_3_2 1 152 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 152 158))))))) (allB_succ' 8 151 158 (Eq.refl Bool.true) (allA_of_3_0 8 151 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 150 158 (Eq.refl Bool.true) (allA_succ_of_gcd 8 150 158 2 4 75 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 158
  (accept_3_2 7 150 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 158 2 3 75 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 158
  (Polychromatic418967fa.accept_13_5_7_2_1_852 5 150 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 150 158 2 2 75 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 150 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 150 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 158 2 1 75 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 158 (accept_3_2 1 150 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 150 158))))))))) (allB_succ' 10 149 158 (Eq.refl Bool.true) (allA_succ_of_accept 9 149 158
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 149 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 149 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 158 (accept_3_2 7 149 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 149 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 149 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 5
  149 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 158 (accept_3_2 4 149
  158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 158 (Polychromatic418967fa.accept_4_3_1_2_1_62
  3 149 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 158
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 149 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 158 (accept_3_2 1 149 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  158)))))))))) (allB_succ' 11 148 158 (Eq.refl Bool.true) (allA_of_3_0 11 148 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 147 158 (Eq.refl Bool.true) (allA_succ_of_accept 11 147 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 158 (accept_3_2 10 147 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 147 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 158 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 147 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 158 (accept_3_2 7 147 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 147 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 147 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 158 (accept_3_2 4 147 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 158 (Polychromatic418967fa.accept_14_3_7_4_1_118 3 147 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 147 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 158 (accept_3_2 1 147 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147 158)))))))))))) (allB_succ' 13 146 158 (Eq.refl Bool.true) (allA_succ_of_gcd 12 146
  158 2 6 73 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  146 158 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 146 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 146 158 2 5 73 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 146 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 146 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 146 158 2 4 73 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 146 158 (accept_3_2 7 146 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146 158 2 3 73 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 146 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 146 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 146 158 2 2 73 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 146 158
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 146 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 146 158 2 1 73 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 146 158 (accept_3_2 1 146 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  158))))))))))))) (allB_succ' 14 145 158 (Eq.refl Bool.true) (allA_of_3_0 14 145 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 144 158 (Eq.refl Bool.true) (allA_succ_of_gcd 14 144 158 2 7 72 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 158 (accept_3_2 13 144 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 158 2 6 72 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 158
  (Polychromatic418967fa.accept_22_11_12_4_1_8675 11 144 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 144 158 2 5 72 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 144 158 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 144 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 158 2 4 72 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 158 (accept_3_2 7 144 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 158 2 3 72 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 158 (Polychromatic418967fa.accept_19_5_11_6_1_1909 5 144 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 158 2 2 72 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 144 158
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 3 144 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 144 158 2 1 72 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 144 158 (accept_3_2 1 144 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  158))))))))))))))) (allB_succ' 16 143 158 (Eq.refl Bool.true) (allA_succ_of_accept 15 143 158
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 143 158 (Polychromatic418967fa.accept_19_14_10_6_1_4372 14 143 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 158 (accept_3_2 13 143 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 143 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 158
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 143 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 158 (accept_3_2 10 143 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 143 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 158 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 143 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 158 (accept_3_2 7 143 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 158 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 143 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 143 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 158 (accept_3_2 4 143 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 143 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 158 (accept_3_2 1 143 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 158)))))))))))))))) (allB_succ' 17 142 158 (Eq.refl Bool.true) (allA_of_3_0 17 142
  158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 141 158 (Eq.refl Bool.true) (allA_succ_of_accept 17 141
  158 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 158 (accept_3_2 16 141 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 141 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 141 158 (Polychromatic418967fa.accept_15_14_6_8_1_1410 14 141 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 158 (accept_3_2 13 141 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 141 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 141 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 158 (accept_3_2 10 141 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 158 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 141 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 158 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 141 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 158 (accept_3_2 7 141 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 158 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 141 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 158 (accept_3_2 4 141 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 141 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 158 (accept_3_2 1 141 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141 158)))))))))))))))))) (allB_succ' 19 140 158 (Eq.refl Bool.true) (allA_succ_of_gcd
  18 140 158 2 9 70 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 140 158 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 140 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 158 2 8 70 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 158 (Polychromatic418967fa.accept_22_15_8_4_1_8680
  15 140 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 158 2 7 70 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 158
  (accept_3_2 13 140 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 158 2 6 70 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 158
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 140 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 140 158 2 5 70 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 140 158 (Polychromatic418967fa.accept_22_9_8_4_1_3821 9 140 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 158 2 4 70 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 140 158 (accept_3_2 7 140 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 140 158 2 3 70 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 140 158 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 140 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 140 158 2 2 70 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 158 (Polychromatic418967fa.accept_13_3_10_2_1_381 3
  140 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 158 2 1 70 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 158 (accept_3_2 1
  140 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140 158))))))))))))))))))) (allB_succ' 20 139 158 (Eq.refl
  Bool.true) (allA_of_3_0 20 139 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 138 158 (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 138 158 2 10 69 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 158 (accept_3_2 19 138 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 158 2 9 69 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 158 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 138 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 158 2 8 69 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 158 (Polychromatic418967fa.accept_7_1_5_4_1_134 15
  138 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 138 158 2 7 69 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 158 (accept_3_2 13
  138 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 158 2 6 69 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 138 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 158 2 5 69 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 138 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 138 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 138 158 2 4 69 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 158 (accept_3_2 7 138 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 138 158 2 3 69 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 138 158 (Polychromatic418967fa.accept_15_5_3_8_1_748 5 138 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 158 2 2 69 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 138 158 (Polychromatic418967fa.accept_12_3_6_2_1_747 3
  138 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 158 2 1 69 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 158 (accept_3_2 1
  138 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138 158))))))))))))))))))))) (allB_succ' 22 137 158
  (Eq.refl Bool.true) (allA_succ_of_accept 21 137 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 158
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 137 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 158 (accept_3_2 19 137 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 158 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 137 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 137 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 158 (accept_3_2 16 137 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 137 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 158
  (Polychromatic418967fa.accept_27_14_2_23_1_8679 14 137 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 137 158 (accept_3_2 13 137 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 137 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 137 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 137 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 158 (accept_3_2 10 137 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 9
  137 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 158
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 137 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 158 (accept_3_2 7 137 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 137 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 158 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 137 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 158 (accept_3_2 4 137 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 137 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 158
  (Polychromatic418967fa.accept_18_2_11_14_1_69 2 137 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 158 (accept_3_2 1 137 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  158)))))))))))))))))))))) (allB_succ' 23 136 158 (Eq.refl Bool.true) (allA_of_3_0 23 136 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 24 135 158 (Eq.refl Bool.true) (allA_succ_of_accept 23 135 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 158 (accept_3_2 22 135 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 135 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 135 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 135 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 135 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 158 (accept_3_2 19 135 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 158 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 135 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 135 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 158 (accept_3_2 16 135 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 135 158 (Polychromatic418967fa.accept_16_15_7_14_1_2883 15 135 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 135 158 (Polychromatic418967fa.accept_22_14_3_4_1_8678 14 135 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 158 (accept_3_2 13 135 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 135 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 158 (accept_3_2 10 135 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  135 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 135 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 158 (Polychromatic418967fa.accept_19_8_2_6_1_8677 8 135 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 158 (accept_3_2 7 135 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 135 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 135 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 158 (accept_3_2 4 135 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 158 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 135 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 158 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 135 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 158 (accept_3_2 1 135 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 135 158)))))))))))))))))))))))) (allB_succ' 25 134 158 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 134 158 2 12 67 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 158 (Polychromatic418967fa.accept_18_5_8_14_1_1282 23 134 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 158 2 11 67 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 158
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 134 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 158 2 10 67 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 158 (accept_3_2 19 134 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 158 2 9 67 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 134 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 134 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 158 2 8 67 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  134 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 134 158 2 7 67 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 134 158 (accept_3_2 13
  134 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 134 158 2 6 67 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 134 158
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 134 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 134 158 2 5 67 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 134 158 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 134 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 134 158 2 4 67 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 134 158 (accept_3_2 7 134 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 134 158 2 3 67 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 134 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 134 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 134 158 2 2 67 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 134 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  134 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 158 2 1 67 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 158 (accept_3_2 1
  134 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134 158))))))))))))))))))))))))) (allB_succ' 26 133 158
  (Eq.refl Bool.true) (allA_of_3_0 26 133 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 132 158 (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 132 158 2 13 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 132 158 (accept_3_2 25 132 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 158 2 12 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 132 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 132 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 158 2 11 66 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 158
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 132 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 158 2 10 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 132 158 (accept_3_2 19 132 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 158 2 9 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 132 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 158 2 8 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 158 (Polychromatic418967fa.accept_10_5_2_8_1_135
  15 132 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 132 158 2 7 66 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 158
  (accept_3_2 13 132 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 158 2 6 66 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 158
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 132 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 132 158 2 5 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 132 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 132 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 158 2 4 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 158 (accept_3_2 7 132 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 132 158 2 3 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 132 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 132 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 158 2 2 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 132 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 3
  132 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 158 2 1 66 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 158 (accept_3_2 1
  132 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132 158))))))))))))))))))))))))))) (allB_succ' 28 131 158
  (Eq.refl Bool.true) (allA_succ_of_accept 27 131 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 131 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 158
  (Polychromatic418967fa.accept_17_9_12_5_1_219 26 131 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 158 (accept_3_2 25 131 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 158 (Polychromatic418967fa.accept_17_7_12_5_1_1580 24 131 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 131 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 158 (accept_3_2 22 131 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 131 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 158
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 131 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 158 (accept_3_2 19 131 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 158 (Polychromatic418967fa.accept_15_3_11_8_1_4186 18 131 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 131 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 158 (accept_3_2 16 131 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 158
  (Polychromatic418967fa.accept_21_14_5_11_1_8676 14 131 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 131 158 (accept_3_2 13 131 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 131 158 (Polychromatic418967fa.accept_13_12_1_2_1_845 12 131 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 158 (Polychromatic418967fa.accept_16_11_3_14_1_5043 11 131
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 158 (accept_3_2 10 131
  158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 158 (Polychromatic418967fa.accept_4_1_3_2_1_3
  9 131 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 158
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 131 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 158 (accept_3_2 7 131 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 158 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 131 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 131 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 158 (accept_3_2 4 131 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 158
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 131 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 158 (accept_3_2 1 131 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  158)))))))))))))))))))))))))))) (allB_succ' 29 130 158 (Eq.refl Bool.true) (allA_of_3_0 29 130 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 129 158 (Eq.refl Bool.true) (allA_succ_of_accept 29 129 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 158 (accept_3_2 28 129 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 129 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 129 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 129 158 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 129 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 158 (accept_3_2 25 129 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 129 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 129 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 158 (accept_3_2 22 129 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 129 158 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 129 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 129 158 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 129 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 158 (accept_3_2 19 129 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 158 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 129 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 158 (accept_3_2 16 129 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 129 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 129 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 129 158 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 129 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 158 (accept_3_2 13 129 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 158 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 129
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 129 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 158 (accept_3_2 10 129 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 158 (Polychromatic418967fa.accept_18_9_3_14_1_3361 9 129 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 158 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 129 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 158 (accept_3_2 7 129 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 158 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 129 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 158 (accept_3_2 4 129 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 129 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 129 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 158 (accept_3_2 1 129 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129 158)))))))))))))))))))))))))))))) (allB_succ' 31 128 158 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 128 158 2 15 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 128 158 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 128 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 158 2 14 64 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 158
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 128 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 158 2 13 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 158 (accept_3_2 25 128 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 158 2 12 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 128 158 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 128 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 158 2 11 64 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 158
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 128 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 158 2 10 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 128 158 (accept_3_2 19 128 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 128 158 2 9 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 128 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 128 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 158 2 8 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 15
  128 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 158 2 7 64 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 158 (accept_3_2 13
  128 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 158 2 6 64 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 158
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 128 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 128 158 2 5 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 128 158 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 128 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 158 2 4 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 158 (accept_3_2 7 128 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 128 158 2 3 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 128 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 128 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 158 2 2 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 3
  128 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 158 2 1 64 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 158 (accept_3_2 1
  128 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128 158))))))))))))))))))))))))))))))) (allB_succ' 32 127
  158 (Eq.refl Bool.true) (allA_of_3_0 32 127 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 126 158
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 126 158 2 16 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 158 (accept_3_2 31 126 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 126 158 2 15 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 126 158 (Polychromatic418967fa.accept_13_3_9_2_1_1486 29 126 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 158 2 14 63 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 158
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 126 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 158 2 13 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 158 (accept_3_2 25 126 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 158 2 12 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 158 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 126 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 158 2 11 63 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 126 158
  (Polychromatic418967fa.accept_11_10_5_4_1_711 21 126 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 126 158 2 10 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 158 (accept_3_2 19 126 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 158 2 9 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 158 (Polychromatic418967fa.accept_15_2_6_8_1_754 17 126 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 158 2 8 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 158 (Polychromatic418967fa.accept_12_3_6_2_1_747
  15 126 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 158 2 7 63 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 158
  (accept_3_2 13 126 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 158 2 6 63 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 158
  (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 126 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 126 158 2 5 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 126 158 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 126 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 158 2 4 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 158 (accept_3_2 7 126 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 126 158 2 3 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 126 158 (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 126 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 158 2 2 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 126 158 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3
  126 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 158 2 1 63 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 158 (accept_3_2 1
  126 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 158))))))))))))))))))))))))))))))))) (allB_succ' 34 125
  158 (Eq.refl Bool.true) (allA_succ_of_accept 33 125 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 125 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 158
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 158 (accept_3_2 31 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 125 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 158 (accept_3_2 28 125 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 125 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 158
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 158 (accept_3_2 25 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 125 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 158 (accept_3_2 22 125 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 125 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 158
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 158 (accept_3_2 19 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 158 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 125 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 158 (accept_3_2 16 125 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 125 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 158
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 14 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 158 (accept_3_2 13 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 125 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 158 (accept_3_2 10 125 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 158
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 158 (accept_3_2 7 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 125 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 158 (accept_3_2 4 125 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 125 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 158
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 158 (accept_3_2 1 125 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  158)))))))))))))))))))))))))))))))))) (allB_succ' 35 124 158 (Eq.refl Bool.true) (allA_of_3_0 35 124 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 123 158 (Eq.refl Bool.true) (allA_succ_of_accept 35 123 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 158 (accept_3_2 34 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 158 (Polychromatic418967fa.accept_19_13_9_6_1_4393 32 123 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 158 (accept_3_2 31 123 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 123 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 158 (accept_3_2 28 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 158 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 158 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 123 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 158 (accept_3_2 25 123 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 158 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 123 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 158 (accept_3_2 22 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 123 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 158 (accept_3_2 19 123 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 123 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 158 (accept_3_2 16 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 158 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 158 (Polychromatic418967fa.accept_13_1_6_2_1_377 14 123 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 158 (accept_3_2 13 123 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 123 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 158 (accept_3_2 10 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 158 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 123 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 158 (accept_3_2 7 123 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 158 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 123 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 158 (accept_3_2 4 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 123 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 123 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 158 (accept_3_2 1 123 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 158)))))))))))))))))))))))))))))))))))) (allB_succ' 37 122 158 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 122 158 2 18 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 158 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 122 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 158 2 17 61 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 158
  (Polychromatic418967fa.accept_13_7_5_2_1_401 33 122 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 158 2 16 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 158 (accept_3_2 31 122 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 158 2 15 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 158 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 122 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 158 2 14 61 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 158
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 122 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 158 2 13 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 158 (accept_3_2 25 122 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 158 2 12 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 158 (Polychromatic418967fa.accept_13_10_5_2_1_1477 23 122 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 158 2 11 61 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 158
  (Polychromatic418967fa.accept_14_7_10_4_1_130 21 122 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 158 2 10 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 158 (accept_3_2 19 122 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 158 2 9 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 122 158 (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 122 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 158 2 8 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 158 (Polychromatic418967fa.accept_7_1_3_4_1_128 15
  122 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 158 2 7 61 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 158 (accept_3_2 13
  122 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 158 2 6 61 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 158
  (Polychromatic418967fa.accept_22_11_12_4_1_8675 11 122 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 122 158 2 5 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 122 158 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 122 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 158 2 4 61 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 158 (accept_3_2 7 122 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122 158 2 3 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 122 158 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 122 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 158 2 2 61 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 158
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 3 122 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 122 158 2 1 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 122 158 (accept_3_2 1 122 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  158))))))))))))))))))))))))))))))))))))) (allB_succ' 38 121 158 (Eq.refl Bool.true) (allA_of_3_0 38 121 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 120 158 (Eq.refl Bool.true) (allA_succ_of_gcd 38 120 158 2 19 60 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 158
  (accept_3_2 37 120 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 158 2 18 60 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 120 158
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 120 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 120 158 2 17 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 120 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 120 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 158 2 16 60 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 158 (accept_3_2 31 120 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 158 2 15 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 29
  120 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 158 2 14 60 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 120 158
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 120 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 120 158 2 13 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 120 158 (accept_3_2 25 120 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 158 2 12 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 120 158 (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 120 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 158 2 11 60 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 158
  (Polychromatic418967fa.accept_17_4_1_5_1_2554 21 120 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 158 2 10 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 120 158 (accept_3_2 19 120 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 158 2 9 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 120 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 158 2 8 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 120 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  120 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 158 2 7 60 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 158 (accept_3_2 13
  120 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 158 2 6 60 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 120 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 158 2 5 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 120 158 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 120 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 158 2 4 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 158 (accept_3_2 7 120 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 120 158 2 3 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 120 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 120 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 158 2 2 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 120 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  120 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 158 2 1 60 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 158 (accept_3_2 1
  120 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120 158))))))))))))))))))))))))))))))))))))))) (allB_succ'
  40 119 158 (Eq.refl Bool.true) (allA_succ_of_accept 39 119 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 119 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 158
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 38 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 158 (accept_3_2 37 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 158 (Polychromatic418967fa.accept_15_6_14_8_1_245 36 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 119 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 158 (accept_3_2 34 119 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 119 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 158
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 158 (accept_3_2 31 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 119 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 158 (accept_3_2 28 119 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 158
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 158 (accept_3_2 25 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 158 (Polychromatic418967fa.accept_18_5_11_14_1_7203 23 119 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 158 (accept_3_2 22 119 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 119 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 158
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 158 (accept_3_2 19 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 158 (Polychromatic418967fa.accept_19_18_5_6_1_2004 18 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 119 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 158 (accept_3_2 16 119 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 158
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 158 (accept_3_2 13 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 158 (Polychromatic418967fa.accept_10_1_9_8_1_123 11 119 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 158 (accept_3_2 10 119 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 119 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 158
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 158 (accept_3_2 7 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 119 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 158 (accept_3_2 4 119 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 158
  (Polychromatic418967fa.accept_11_2_9_4_1_310 2 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 158 (accept_3_2 1 119 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  158)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 118 158 (Eq.refl Bool.true) (allA_of_3_0 41 118 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 117 158 (Eq.refl Bool.true) (allA_succ_of_accept 41 117 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 158 (accept_3_2 40 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 117 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 117 158 (Polychromatic418967fa.accept_25_13_17_8_1_8674 38 117 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 158 (accept_3_2 37 117 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 158 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 117 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 158 (accept_3_2 34 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 158 (Polychromatic418967fa.accept_15_3_12_8_1_738 33 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 158 (Polychromatic418967fa.accept_22_10_7_4_1_7008 32 117 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 158 (accept_3_2 31 117 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 117 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 158 (accept_3_2 28 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 117 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 117 158 (Polychromatic418967fa.accept_15_11_12_8_1_739 26 117 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 158 (accept_3_2 25 117 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 158 (Polychromatic418967fa.accept_17_7_15_5_1_3649 24 117
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 158 (accept_3_2 22 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 117 158 (Polychromatic418967fa.accept_18_3_9_14_1_2219 21 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 158 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 117 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 158 (accept_3_2 19 117 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 158 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 117 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 158 (accept_3_2 16 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 117 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 117 158 (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 117 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 158 (accept_3_2 13 117 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 158 (Polychromatic418967fa.accept_25_12_17_8_1_8673 12 117
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 158 (accept_3_2 10 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  117 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 158 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 117 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 158 (accept_3_2 7 117 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 158 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 117 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 158 (accept_3_2 4 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 117 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 117 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 158 (accept_3_2 1 117 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 117 158)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 116 158 (Eq.refl
  Bool.true) (allA_succ_of_gcd 42 116 158 2 21 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 116 158 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 116 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 158 2 20 58 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 158
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 116 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 158 2 19 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 158 (accept_3_2 37 116 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 158 2 18 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 116 158 (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 116 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 158 2 17 58 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 158
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 116 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 116 158 2 16 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 116 158 (accept_3_2 31 116 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 116 158 2 15 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 116 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 116 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 158 2 14 58 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 158
  (Polychromatic418967fa.accept_13_1_12_2_1_384 27 116 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 116 158 2 13 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 116 158 (accept_3_2 25 116 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 116 158 2 12 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 116 158 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 116 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 158 2 11 58 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 158
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 116 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 158 2 10 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 116 158 (accept_3_2 19 116 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 116 158 2 9 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 116 158 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 116 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 158 2 8 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  116 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 158 2 7 58 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 158 (accept_3_2 13
  116 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 158 2 6 58 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 158
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 116 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 116 158 2 5 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 116 158 (Polychromatic418967fa.accept_16_9_4_14_1_1878 9 116 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 158 2 4 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 158 (accept_3_2 7 116 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 116 158 2 3 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 116 158 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 116 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 158 2 2 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 3
  116 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 158 2 1 58 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 158 (accept_3_2 1
  116 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116 158)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 115 158 (Eq.refl Bool.true) (allA_of_3_0 44 115 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 45 114 158 (Eq.refl Bool.true) (allA_succ_of_gcd 44 114 158 2 22 57 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 158 (accept_3_2 43 114 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 114 158 2 21 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 114 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 41
  114 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 158 2 20 57 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 158
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 114 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 158 2 19 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 158 (accept_3_2 37 114 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 158 2 18 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 158 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 114 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 158 2 17 57 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 158
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 114 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 158 2 16 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 158 (accept_3_2 31 114 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 158 2 15 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 114 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 158 2 14 57 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 158
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 114 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 158 2 13 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 158 (accept_3_2 25 114 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 158 2 12 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 158 (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 114 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 158 2 11 57 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 158
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 114 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 158 2 10 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 158 (accept_3_2 19 114 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 158 2 9 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 158 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 114 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 158 2 8 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 158 (Polychromatic418967fa.accept_12_3_6_2_1_747
  15 114 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 114 158 2 7 57 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 158
  (accept_3_2 13 114 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 158 2 6 57 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 158
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 114 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 114 158 2 5 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 114 158 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 114 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 114 158 2 4 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 158 (accept_3_2 7 114 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 114 158 2 3 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 114 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 114 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 158 2 2 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 114 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 3
  114 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 158 2 1 57 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 158 (accept_3_2 1
  114 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 158)))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 46 113 158 (Eq.refl Bool.true) (allA_succ_of_accept 45 113 158 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 158
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 158 (accept_3_2 43 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 158 (Polychromatic418967fa.accept_13_3_9_2_1_1486 42 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 158 (Polychromatic418967fa.accept_10_1_3_8_1_136 41 113 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 158 (accept_3_2 40 113 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 113 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 158
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 158 (accept_3_2 37 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 158 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 113 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 158 (accept_3_2 34 113 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 113 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 158
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 158 (accept_3_2 31 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 158 (Polychromatic418967fa.accept_19_11_18_6_1_3113 30 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 158 (Polychromatic418967fa.accept_11_7_3_4_1_729 29 113 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 158 (accept_3_2 28 113 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 113 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 158
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 158 (accept_3_2 25 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 113 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 158 (accept_3_2 22 113 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 158
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 158 (accept_3_2 19 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 158 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 113 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 158 (accept_3_2 16 113 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 113 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 158
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 14 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 158 (accept_3_2 13 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 113 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 158 (accept_3_2 10 113 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 158
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 158 (accept_3_2 7 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 158 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 113 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 158 (accept_3_2 4 113 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 113 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 158
  (Polychromatic418967fa.accept_20_2_13_18_1_5615 2 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 158 (accept_3_2 1 113 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  158)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 112 158 (Eq.refl Bool.true) (allA_of_3_0 47 112 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 111 158 (Eq.refl Bool.true) (allA_succ_of_accept 47 111 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 158 (accept_3_2 46 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 111 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 158 (accept_3_2 43 111 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 111 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 158 (accept_3_2 40 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 158 (Polychromatic418967fa.accept_10_9_1_8_1_755 39 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 111 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 158 (accept_3_2 37 111 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 158 (Polychromatic418967fa.accept_16_4_15_14_1_5056 36 111 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 158 (accept_3_2 34 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 158 (Polychromatic418967fa.accept_15_2_6_8_1_754 32 111 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 158 (accept_3_2 31 111 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 111 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 158 (accept_3_2 28 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 158 (Polychromatic418967fa.accept_18_9_3_14_1_3361 27 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 111 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 158 (accept_3_2 25 111 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 111 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 158 (accept_3_2 22 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 111 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 158 (accept_3_2 19 111 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 111 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 158 (accept_3_2 16 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 158 (Polychromatic418967fa.accept_15_14_6_8_1_1410 14 111 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 158 (accept_3_2 13 111 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 111 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 158 (accept_3_2 10 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 158 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 111 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 158 (accept_3_2 7 111 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 111 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 158 (accept_3_2 4 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 111 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 111 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 158 (accept_3_2 1 111 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111 158)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 110 158 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 110 158 2 24 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 110 158 (Polychromatic418967fa.accept_13_8_6_2_1_865 47 110 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 158 2 23 55 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 158
  (Polychromatic418967fa.accept_20_5_10_18_1_5622 45 110 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 110 158 2 22 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 110 158 (accept_3_2 43 110 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 158 2 21 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 158 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 110 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 158 2 20 55 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 158
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 110 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 158 2 19 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 158 (accept_3_2 37 110 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 158 2 18 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 110 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 158 2 17 55 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 158
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 110 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 158 2 16 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 158 (accept_3_2 31 110 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 158 2 15 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 158 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 110 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 158 2 14 55 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 158
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 110 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 158 2 13 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 158 (accept_3_2 25 110 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 158 2 12 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 110 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 158 2 11 55 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 158
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 110 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 158 2 10 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 158 (accept_3_2 19 110 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 158 2 9 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 110 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 158 2 8 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 158 (Polychromatic418967fa.accept_7_1_5_4_1_134 15
  110 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 158 2 7 55 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 158 (accept_3_2 13
  110 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 158 2 6 55 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 158
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 110 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 158 2 5 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 110 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 110 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 158 2 4 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 158 (accept_3_2 7 110 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 110 158 2 3 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 110 158 (Polychromatic418967fa.accept_19_5_15_6_1_1986 5 110 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 110 158 2 2 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 3
  110 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 158 2 1 55 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 158 (accept_3_2 1
  110 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110 158)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 109 158 (Eq.refl Bool.true) (allA_of_3_0 50 109 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 51 108 158 (Eq.refl Bool.true) (allA_succ_of_gcd 50 108 158 2 25 54 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 158 (accept_3_2 49 108 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 108 158 2 24 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 108 158 (Polychromatic418967fa.accept_19_9_13_6_1_7198
  47 108 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 158 2 23 54 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 108 158
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 45 108 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 108 158 2 22 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 108 158 (accept_3_2 43 108 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 158 2 21 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 158 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 108 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 158 2 20 54 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 108 158
  (Polychromatic418967fa.accept_15_9_3_8_1_3155 39 108 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 108 158 2 19 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 108 158 (accept_3_2 37 108 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 158 2 18 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 108 158 (Polychromatic418967fa.accept_11_2_9_4_1_310 35 108 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 158 2 17 54 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 158
  (Polychromatic418967fa.accept_20_13_8_18_1_8672 33 108 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 108 158 2 16 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 108 158 (accept_3_2 31 108 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 158 2 15 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 158 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 108 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 158 2 14 54 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 108 158
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 108 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 108 158 2 13 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 108 158 (accept_3_2 25 108 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 158 2 12 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 108 158 (Polychromatic418967fa.accept_19_4_13_6_1_8671 23 108 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 158 2 11 54 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 158
  (Polychromatic418967fa.accept_14_7_10_4_1_130 21 108 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 158 2 10 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 108 158 (accept_3_2 19 108 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 158 2 9 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 158 (Polychromatic418967fa.accept_19_17_13_6_1_8670 17 108 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 158 2 8 54 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 158
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 108 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 108 158 2 7 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 108 158 (accept_3_2 13 108 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  108 158 2 6 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 108 158 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 108 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 108 158 2 5 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 108 158 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 108 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 158 2 4 54 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 158 (accept_3_2 7 108 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 158 2 3 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 158 (Polychromatic418967fa.accept_13_5_4_2_1_846 5 108 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 158 2 2 54 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 158
  (Polychromatic418967fa.accept_17_3_6_5_1_8669 3 108 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 108 158 2 1 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 158 (accept_3_2 1 108 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  158))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 107 158 (Eq.refl Bool.true) (allA_succ_of_accept
  51 107 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 107 158 (Polychromatic418967fa.accept_13_11_3_2_1_863 50 107 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 158 (accept_3_2 49 107 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 107 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 158
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 158 (accept_3_2 46 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 158 (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 107 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 158 (accept_3_2 43 107 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 107 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 158 (accept_3_2 40 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 107 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 158 (accept_3_2 37 107 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 158 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 107 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 158
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 158 (accept_3_2 34 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 158 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 107 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 158 (accept_3_2 31 107 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 107 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 158 (accept_3_2 28 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 107 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 158 (accept_3_2 25 107 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 107 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 158
  (Polychromatic418967fa.accept_11_1_8_4_1_717 23 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 158 (accept_3_2 22 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 107 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 158 (accept_3_2 19 107 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 158 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 107 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 158 (accept_3_2 16 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 158 (Polychromatic418967fa.accept_13_1_3_2_1_1429 14 107 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 158 (accept_3_2 13 107 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 107 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 158
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 158 (accept_3_2 10 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 158 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 107 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 158 (accept_3_2 7 107 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 107 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 158 (accept_3_2 4 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 107 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 158 (accept_3_2 1 107 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 158)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 106 158
  (Eq.refl Bool.true) (allA_of_3_0 53 106 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 105 158 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 105 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 105 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 158 (accept_3_2 52 105 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 105 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 158
  (Polychromatic418967fa.accept_19_12_10_6_1_8668 50 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 105 158 (accept_3_2 49 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 105 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 105 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 105 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 158 (accept_3_2 46 105 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 158 (Polychromatic418967fa.accept_13_6_1_2_1_1464
  45 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 158
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 158 (accept_3_2 43 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 105 158 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 105 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 158 (accept_3_2 40 105 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 105 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 105 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 158
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 158 (accept_3_2 37 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 105 158 (Polychromatic418967fa.accept_16_4_9_14_1_3883 36 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 105 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 105 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 158 (accept_3_2 34 105 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 158 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 105 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 158
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 158 (accept_3_2 31 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 105 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 105 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 158 (accept_3_2 28 105 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 105 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 158
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 158 (accept_3_2 25 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 105 158 (Polychromatic418967fa.accept_11_2_6_4_1_3028 24 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 105 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 158 (accept_3_2 22 105 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 105 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 158
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 158 (accept_3_2 19 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 105 158 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 105 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 158 (accept_3_2 16 105 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 105 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 158
  (Polychromatic418967fa.accept_19_14_10_6_1_4372 14 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 105 158 (accept_3_2 13 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 105 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 105 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 105 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 158 (accept_3_2 10 105 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 158 (Polychromatic418967fa.accept_13_9_1_2_1_2952
  9 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 158
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 158 (accept_3_2 7 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  105 158 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 158 (accept_3_2 4 105 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 158
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 158 (accept_3_2 1 105 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  158)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 104 158 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 104 158 2 27 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 104 158 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 104 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 158 2 26 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 51
  104 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 104 158 2 25 52 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 104 158 (accept_3_2 49
  104 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 104 158 2 24 52 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 104 158
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 104 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 104 158 2 23 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 104 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 104 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 104 158 2 22 52 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 104 158 (accept_3_2 43 104 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 104 158 2 21 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 104 158 (Polychromatic418967fa.accept_12_5_8_2_1_309
  41 104 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 158 2 20 52 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 158
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 104 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 158 2 19 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 158 (accept_3_2 37 104 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 158 2 18 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 104 158 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 104 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 158 2 17 52 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 158
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 104 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 104 158 2 16 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 104 158 (accept_3_2 31 104 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 104 158 2 15 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 104 158 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 104 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 158 2 14 52 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 158
  (Polychromatic418967fa.accept_21_6_20_11_1_7067 27 104 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 104 158 2 13 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 104 158 (accept_3_2 25 104 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 158 2 12 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 104 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 104 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 158 2 11 52 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 158
  (Polychromatic418967fa.accept_11_10_5_4_1_711 21 104 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 158 2 10 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 104 158 (accept_3_2 19 104 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 104 158 2 9 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 104 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 158 2 8 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 158 (Polychromatic418967fa.accept_19_15_9_6_1_8667
  15 104 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 158 2 7 52 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 158
  (accept_3_2 13 104 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 158 2 6 52 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 158
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 104 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 158 2 5 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 104 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 104 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 158 2 4 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 158 (accept_3_2 7 104 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 104 158 2 3 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 104 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 104 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 158 2 2 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 3
  104 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 158 2 1 52 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 158 (accept_3_2 1
  104 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  158))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 103 158 (Eq.refl Bool.true) (allA_of_3_0 56
  103 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 102 158 (Eq.refl Bool.true) (allA_succ_of_gcd 56 102
  158 2 28 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55
  102 158 (accept_3_2 55 102 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 102 158 2 27 51 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 102 158
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 102 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 102 158 2 26 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 102 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 102 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 102 158 2 25 51 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 158 (accept_3_2 49 102 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 102 158 2 24 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 102 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 47
  102 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 158 2 23 51 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 158
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 102 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 158 2 22 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 158 (accept_3_2 43 102 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 158 2 21 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 158 (Polychromatic418967fa.accept_15_11_12_8_1_739 41 102 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 158 2 20 51 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 158
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 102 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 158 2 19 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 158 (accept_3_2 37 102 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 158 2 18 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 158 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 102 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 158 2 17 51 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 158
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 102 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 158 2 16 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 158 (accept_3_2 31 102 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 158 2 15 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 102 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 158 2 14 51 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 158
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 102 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 158 2 13 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 158 (accept_3_2 25 102 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 158 2 12 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 158 (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 102 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 158 2 11 51 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 158
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 102 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 158 2 10 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 158 (accept_3_2 19 102 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 158 2 9 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 158 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 102 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 158 2 8 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  102 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 158 2 7 51 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 158 (accept_3_2 13
  102 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 158 2 6 51 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 102 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 158 2 5 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 102 158 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 102 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 158 2 4 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 158 (accept_3_2 7 102 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 102 158 2 3 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 102 158 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 102 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 158 2 2 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 102 158 (Polychromatic418967fa.accept_12_3_6_2_1_747 3
  102 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 158 2 1 51 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 158 (accept_3_2 1
  102 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  158))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 101 158 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 101 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 101 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 101
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 158 (accept_3_2 55 101
  158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 158
  (Polychromatic418967fa.accept_23_8_9_20_1_5177 54 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 101 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 101 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 158 (accept_3_2 52 101 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 101 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 101 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 158 (Polychromatic418967fa.accept_7_1_3_4_1_128
  50 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 158 (accept_3_2 49
  101 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 158
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 101 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 101 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 158 (accept_3_2 46 101 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 101 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 158 (Polychromatic418967fa.accept_9_8_2_5_1_237
  44 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 158 (accept_3_2 43
  101 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 158
  (Polychromatic418967fa.accept_9_6_2_5_1_506 42 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 101 158 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 101 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 158 (accept_3_2 40 101 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 101 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 101 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 158
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 38 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 101 158 (accept_3_2 37 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 101 158 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 101 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 101 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 158 (accept_3_2 34 101 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 158
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 158 (accept_3_2 31 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 158 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 101 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 158 (accept_3_2 28 101 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 101 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 158
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 158 (accept_3_2 25 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 101 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 158 (accept_3_2 22 101 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 158
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 158 (accept_3_2 19 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 158 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 101 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 158 (accept_3_2 16 101 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 101 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 158
  (Polychromatic418967fa.accept_22_14_13_4_1_8640 14 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 101 158 (accept_3_2 13 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 101 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 101 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 101 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 158 (accept_3_2 10 101 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 9
  101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 158
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 158 (accept_3_2 7 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 158 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 158 (Polychromatic418967fa.accept_13_5_10_2_1_856 5 101 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 158 (accept_3_2 4 101 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 101 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 158
  (Polychromatic418967fa.accept_17_2_16_5_1_1584 2 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 158 (accept_3_2 1 101 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 100 158 (Eq.refl Bool.true) (allA_of_3_0
  59 100 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 99 158 (Eq.refl Bool.true) (allA_succ_of_accept 59
  99 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 99 158 (accept_3_2 58 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 99 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 99 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 158 (Polychromatic418967fa.accept_22_12_11_4_1_7003 56 99
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 158 (accept_3_2 55 99 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 99 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 54
  99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 99 158 (accept_3_2 52 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  99 158 (Polychromatic418967fa.accept_10_1_9_8_1_123 51 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 99 158 (Polychromatic418967fa.accept_19_12_4_6_1_7163 50 99 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 158 (accept_3_2 49 99 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 158 (Polychromatic418967fa.accept_15_3_9_8_1_3164 48 99 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 158 (accept_3_2 46 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  99 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 99 158 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 99 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 158 (accept_3_2 43 99 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 99 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 158 (accept_3_2 40 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  99 158 (Polychromatic418967fa.accept_14_11_1_4_1_4445 39 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 99 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 99 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 158 (accept_3_2 37 99 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 158 (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 99 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 158 (accept_3_2 34 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  99 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 99 158 (Polychromatic418967fa.accept_13_6_8_2_1_1484 32 99 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 158 (accept_3_2 31 99 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 99 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 158 (accept_3_2 28 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  99 158 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 99 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 99 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 158 (accept_3_2 25 99 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 99 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 158 (accept_3_2 22 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  99 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 158 (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 99 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 158 (accept_3_2 19 99 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 99 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 158 (accept_3_2 16 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 158 (Polychromatic418967fa.accept_19_15_4_6_1_8666 15 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 158 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 99 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 158 (accept_3_2 13 99 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 99 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 158
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 158 (accept_3_2 10 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 158 (Polychromatic418967fa.accept_26_8_21_2_1_8665 8 99 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 158 (accept_3_2 7 99 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 99 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 99
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 158 (accept_3_2 4 99 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 158
  (Polychromatic418967fa.accept_15_2_9_8_1_736 2 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 158 (accept_3_2 1 99 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 98 158 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 98 158 2 30 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 98 158 (Polychromatic418967fa.accept_17_8_13_5_1_1597 59 98 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 98 158 2 29 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 98 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 57
  98 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 98 158 2 28 49 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 98 158 (accept_3_2 55
  98 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 98 158 2 27 49 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 98 158
  (Polychromatic418967fa.accept_25_3_23_8_1_8664 53 98 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 98 158 2 26 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 98 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 98 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 98 158 2 25 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 98 158 (accept_3_2 49 98 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 98 158 2 24 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 98 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 98 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 158 2 23 49 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 158
  (Polychromatic418967fa.accept_19_7_3_6_1_8663 45 98 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 98 158 2 22 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 98 158 (accept_3_2 43 98 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98
  158 2 21 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  98 158 (Polychromatic418967fa.accept_18_5_8_14_1_1282 41 98 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 98 158 2 20 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 98 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 98 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 98 158 2 19 49 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 98 158 (accept_3_2 37 98 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 98 158 2 18 49 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 98 158
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 98 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 98 158 2 17 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 98 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 98 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 98 158 2 16 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 98 158 (accept_3_2 31 98 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 98 158 2 15 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 98 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 98 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 158 2 14 49 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 158
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 98 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 158 2 13 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 98 158 (accept_3_2 25 98 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98
  158 2 12 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  98 158 (Polychromatic418967fa.accept_18_5_8_14_1_1282 23 98 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 98 158 2 11 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 98 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 98 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 98 158 2 10 49 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 98 158 (accept_3_2 19 98 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98 158 2 9 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 98 158 (Polychromatic418967fa.accept_19_17_3_6_1_8662
  17 98 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 158 2 8 49 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 158
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 98 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 98 158 2 7 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 98 158 (accept_3_2 13 98 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98
  158 2 6 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  98 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 98 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 98 158 2 5 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 98 158 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 98 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 158 2 4 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 158 (accept_3_2 7 98 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 158 2 3 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 98 158 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 98 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 158 2 2 49 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 158
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 98 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 98 158 2 1 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 98 158 (accept_3_2 1 98 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  158))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 97 158 (Eq.refl Bool.true)
  (allA_of_3_0 62 97 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 96 158 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 96 158 2 31 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 96 158 (accept_3_2 61 96 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96
  158 2 30 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  96 158 (Polychromatic418967fa.accept_13_7_5_2_1_401 59 96 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 96 158 2 29 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 96 158 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 96 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 96 158 2 28 48 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 158 (accept_3_2 55 96 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 158 2 27 48 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 158
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 96 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 96 158 2 26 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 96 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 96 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 96 158 2 25 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 158 (accept_3_2 49 96 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 158 2 24 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 96 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 158 2 23 48 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 158
  (Polychromatic418967fa.accept_11_1_8_4_1_717 45 96 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 96 158 2 22 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 96 158 (accept_3_2 43 96 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96
  158 2 21 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  96 158 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 96 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 96 158 2 20 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 96 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 96 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 158 2 19 48 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 158 (accept_3_2 37 96 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 158 2 18 48 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 158
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 96 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 96 158 2 17 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 96 158 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 96 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 96 158 2 16 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 158 (accept_3_2 31 96 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 158 2 15 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 158 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 96 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 158 2 14 48 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 158
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 96 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 96 158 2 13 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 96 158 (accept_3_2 25 96 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96
  158 2 12 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  96 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 96 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 96 158 2 11 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 96 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 96 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 96 158 2 10 48 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 158 (accept_3_2 19 96 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 158 2 9 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 158 (Polychromatic418967fa.accept_9_8_6_5_1_513 17
  96 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 158 2 8 48 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 158
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 96 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 96 158 2 7 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 96 158 (accept_3_2 13 96 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96
  158 2 6 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  96 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 96 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 96 158 2 5 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 96 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 96 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 158 2 4 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 158 (accept_3_2 7 96 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 158 2 3 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 96 158 (Polychromatic418967fa.accept_19_5_1_6_1_4361 5 96 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 158 2 2 48 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 96 158
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 96 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 96 158 2 1 48 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 158 (accept_3_2 1 96 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  158))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 95 158 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 95 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 95 158 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 95 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 158 (accept_3_2 61 95 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 158
  (Polychromatic418967fa.accept_27_6_14_23_1_8661 60 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 95 158 (Polychromatic418967fa.accept_15_14_5_8_1_3175 59 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 95 158 (accept_3_2 58 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 95 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 95 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 95 158 (Polychromatic418967fa.accept_12_8_11_2_1_1277
  56 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 158 (accept_3_2 55
  95 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 158
  (Polychromatic418967fa.accept_22_10_7_4_1_7008 54 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 95 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 158 (accept_3_2 52 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 95 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 95 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 95 158 (Polychromatic418967fa.accept_13_11_4_2_1_2954
  50 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 158 (accept_3_2 49
  95 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 158
  (Polychromatic418967fa.accept_15_3_5_8_1_1387 48 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 95 158 (Polychromatic418967fa.accept_10_7_5_8_1_1167 47 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 158 (accept_3_2 46 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 95 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 95 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 95 158 (Polychromatic418967fa.accept_12_8_11_2_1_1277
  44 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 158 (accept_3_2 43
  95 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 158
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 95 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 95 158 (accept_3_2 40 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 95 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 158 (Polychromatic418967fa.accept_13_12_4_2_1_2955
  38 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 158 (accept_3_2 37
  95 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 158
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 95 158 (Polychromatic418967fa.accept_14_7_11_4_1_3455 35 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 95 158 (accept_3_2 34 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 95 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 95 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 158 (Polychromatic418967fa.accept_10_2_5_8_1_139
  32 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 158 (accept_3_2 31
  95 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 158
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 95 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 158 (accept_3_2 28 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 95 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 158 (Polychromatic418967fa.accept_15_11_5_8_1_3157
  26 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 158 (accept_3_2 25
  95 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 158
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 95 158 (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 158 (accept_3_2 22 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 95 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 95 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 158 (Polychromatic418967fa.accept_12_8_11_2_1_1277
  20 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 158 (accept_3_2 19
  95 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 158
  (Polychromatic418967fa.accept_13_5_4_2_1_846 18 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 95 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 158 (accept_3_2 16 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 95 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 158 (Polychromatic418967fa.accept_11_3_7_4_1_1133
  14 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 158 (accept_3_2 13
  95 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 158
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 95 158 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 158 (accept_3_2 10 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 95 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 95 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 158 (Polychromatic418967fa.accept_11_8_7_4_1_3011 8
  95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 158 (accept_3_2 7 95 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 158 (Polychromatic418967fa.accept_13_6_4_2_1_1433 6
  95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 158 (accept_3_2 4 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  158 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 158 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 158 (accept_3_2 1 95 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95 158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 94 158
  (Eq.refl Bool.true) (allA_of_3_0 65 94 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 93 158 (Eq.refl
  Bool.true) (allA_succ_of_accept 65 93 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 158 (accept_3_2 64 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 93 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 158
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 158 (accept_3_2 61 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 158 (accept_3_2 58 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 158 (Polychromatic418967fa.accept_15_12_3_8_1_5245 57 93 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 158 (accept_3_2 55 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 158 (accept_3_2 52 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 93 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 158
  (Polychromatic418967fa.accept_15_5_3_8_1_748 50 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 158 (accept_3_2 49 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 158 (accept_3_2 46 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 158 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 93 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 158
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 158 (accept_3_2 43 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 158 (accept_3_2 40 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 93 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 158 (accept_3_2 37 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 158 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 158 (accept_3_2 34 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 93 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 158
  (Polychromatic418967fa.accept_11_10_5_4_1_711 32 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 158 (accept_3_2 31 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 158 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 158 (accept_3_2 28 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 158
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 158 (accept_3_2 25 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 158 (accept_3_2 22 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 158 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 93 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 158
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 158 (accept_3_2 19 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 158 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 158 (accept_3_2 16 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 158
  (Polychromatic418967fa.accept_25_14_18_8_1_8660 14 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 158 (accept_3_2 13 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 158 (accept_3_2 10 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 158 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 93 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 158
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 158 (accept_3_2 7 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  158 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 93 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 158 (accept_3_2 4 93 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 93
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 158 (accept_3_2 1 93 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 92 158 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 92 158 2 33 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 92 158 (Polychromatic418967fa.accept_10_5_2_8_1_135 65 92 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 92 158 2 32 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 92 158 (Polychromatic418967fa.accept_17_12_7_5_1_8659
  63 92 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 158 2 31 46 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 158 (accept_3_2 61
  92 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 158 2 30 46 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 158
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 92 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 92 158 2 29 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 92 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 92 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 92 158 2 28 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 92 158 (accept_3_2 55 92 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92 158 2 27 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 92 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 92 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 92 158 2 26 46 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 92 158
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 92 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 92 158 2 25 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 92 158 (accept_3_2 49 92 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92
  158 2 24 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  92 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 92 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 92 158 2 23 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 92 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 92 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 158 2 22 46 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 158 (accept_3_2 43 92 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 158 2 21 46 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 158
  (Polychromatic418967fa.accept_12_5_8_2_1_309 41 92 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 92 158 2 20 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 92 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 92 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 92 158 2 19 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 92 158 (accept_3_2 37 92 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92 158 2 18 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 92 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 92 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 158 2 17 46 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 158
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 92 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 92 158 2 16 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 92 158 (accept_3_2 31 92 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92
  158 2 15 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  92 158 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 92 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 92 158 2 14 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 92 158 (Polychromatic418967fa.accept_19_8_16_6_1_5804 27 92 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 158 2 13 46 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 158 (accept_3_2 25 92 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 158 2 12 46 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 92 158
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 92 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 92 158 2 11 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 92 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 92 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 92 158 2 10 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 92 158 (accept_3_2 19 92 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92 158 2 9 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 92 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 92 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 92 158 2 8 46 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 92 158
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 92 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 92 158 2 7 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 92 158 (accept_3_2 13 92 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92
  158 2 6 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  92 158 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 92 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 92 158 2 5 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 92 158 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 92 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 158 2 4 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 158 (accept_3_2 7 92 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 158 2 3 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 92 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 92 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 158 2 2 46 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 158
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 92 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 92 158 2 1 46 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 92 158 (accept_3_2 1 92 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  158))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 91 158 (Eq.refl Bool.true)
  (allA_of_3_0 68 91 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 90 158 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 90 158 2 34 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 90 158 (accept_3_2 67 90 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90
  158 2 33 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  90 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 90 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 90 158 2 32 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 90 158 (Polychromatic418967fa.accept_12_3_6_2_1_747 63 90 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 90 158 2 31 45 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 158 (accept_3_2 61 90 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 158 2 30 45 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 158
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 90 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 90 158 2 29 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 90 158 (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 90 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 90 158 2 28 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 90 158 (accept_3_2 55 90 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 90 158 2 27 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 158 (Polychromatic418967fa.accept_11_9_2_4_1_707 53 90 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 158 2 26 45 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 158
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 90 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 158 2 25 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 158 (accept_3_2 49 90 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90
  158 2 24 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  90 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 90 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 90 158 2 23 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 90 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 90 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 90 158 2 22 45 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 158 (accept_3_2 43 90 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 158 2 21 45 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 158
  (Polychromatic418967fa.accept_21_20_6_11_1_2623 41 90 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 90 158 2 20 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 90 158 (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 90 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 158 2 19 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 158 (accept_3_2 37 90 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 158 2 18 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 90 158 (Polychromatic418967fa.accept_20_15_10_18_1_8658 35 90
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 158 2 17 45 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 158
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 90 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 158 2 16 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 90 158 (accept_3_2 31 90 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90
  158 2 15 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  90 158 (Polychromatic418967fa.accept_13_3_12_2_1_385 29 90 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 90 158 2 14 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 90 158 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 90 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 158 2 13 45 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 158 (accept_3_2 25 90 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 158 2 12 45 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 158
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 90 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 158 2 11 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 90 158 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 90 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 158 2 10 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 158 (accept_3_2 19 90 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 158 2 9 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 90 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 90 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 158 2 8 45 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 158
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 90 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 90 158 2 7 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 90 158 (accept_3_2 13 90 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90
  158 2 6 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  90 158 (Polychromatic418967fa.accept_19_11_14_6_1_4378 11 90 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 90 158 2 5 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 90 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 90 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 158 2 4 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 158 (accept_3_2 7 90 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 158 2 3 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 90 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 90 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 158 2 2 45 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 158
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 90 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 158 2 1 45 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 158 (accept_3_2 1 90 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  158))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 89 158 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 89 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 89 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 89 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 68 89 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 158 (accept_3_2 67 89 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 66
  89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 158
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 158 (accept_3_2 64 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 158 (Polychromatic418967fa.accept_7_6_5_4_1_297 62 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 158 (accept_3_2 61 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 89 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 158 (accept_3_2 58 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 158 (accept_3_2 55 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 158 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 89 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 158
  (Polychromatic418967fa.accept_16_5_9_14_1_5051 53 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 158 (accept_3_2 52 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 158 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 158 (accept_3_2 49 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 158 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 89 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 158 (accept_3_2 46 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 158 (accept_3_2 43 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 89 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 158
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 158 (accept_3_2 40 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 158 (accept_3_2 37 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 158 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 89 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 158 (accept_3_2 34 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 158 (accept_3_2 31 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 89 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 158
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 158 (accept_3_2 28 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 158 (Polychromatic418967fa.accept_19_7_13_6_1_1914 26 89 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 158 (accept_3_2 25 89 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 89 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 158 (accept_3_2 22 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 158 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 158 (accept_3_2 19 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 158 (Polychromatic418967fa.accept_17_1_4_5_1_3501 18 89 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 158
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 158 (accept_3_2 16 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 158 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 158 (accept_3_2 13 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 89 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 158 (accept_3_2 10 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 158 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 158 (accept_3_2 7 89 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 158 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 89 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 158
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 158 (accept_3_2 4 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 89 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 158 (accept_3_2 1 89 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 88
  158 (Eq.refl Bool.true) (allA_of_3_0 71 88 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 87 158 (Eq.refl
  Bool.true) (allA_succ_of_accept 71 87 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 158 (accept_3_2 70 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 87 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 158
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 68 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 158 (accept_3_2 67 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 158 (accept_3_2 64 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 158 (Polychromatic418967fa.accept_13_11_9_2_1_2969 63 87 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 158
  (Polychromatic418967fa.accept_7_6_3_4_1_294 62 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 158 (accept_3_2 61 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 158 (Polychromatic418967fa.accept_11_5_10_4_1_1157 60 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 158 (accept_3_2 58 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 87 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 158
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 158 (accept_3_2 55 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 158 (accept_3_2 52 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 158 (Polychromatic418967fa.accept_19_13_11_6_1_3128 51 87 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 158
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 158 (accept_3_2 49 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 158 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 158 (accept_3_2 46 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 87 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 158
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 158 (accept_3_2 43 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 158 (accept_3_2 40 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 87 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 158
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 158 (accept_3_2 37 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 158 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 158 (accept_3_2 34 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 158
  (Polychromatic418967fa.accept_13_6_9_2_1_838 32 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 158 (accept_3_2 31 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 158 (accept_3_2 28 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 158 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 87 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 158
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 158 (accept_3_2 25 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 158 (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 158 (accept_3_2 22 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 158
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 158 (accept_3_2 19 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 158 (accept_3_2 16 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 158 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 87 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 158
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 14 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 158 (accept_3_2 13 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 158 (accept_3_2 10 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 158
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 158 (accept_3_2 7 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  158 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 158 (accept_3_2 4 87 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 87 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  87 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 158 (accept_3_2 1 87 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 86 158 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 86 158 2 36 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 86 158 (Polychromatic418967fa.accept_13_6_8_2_1_1484 71 86 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 158 2 35 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 69
  86 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 86 158 2 34 43 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 86 158 (accept_3_2 67
  86 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 86 158 2 33 43 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 86 158
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 65 86 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 86 158 2 32 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 86 158 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 86 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 86 158 2 31 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 86 158 (accept_3_2 61 86 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 86 158 2 30 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 86 158 (Polychromatic418967fa.accept_13_7_8_2_1_1483 59 86 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 86 158 2 29 43 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 86 158
  (Polychromatic418967fa.accept_11_2_9_4_1_310 57 86 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 86 158 2 28 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 86 158 (accept_3_2 55 86 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 86
  158 2 27 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  86 158 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 86 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 86 158 2 26 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 86 158 (Polychromatic418967fa.accept_14_9_2_4_1_1814 51 86 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 86 158 2 25 43 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 86 158 (accept_3_2 49 86 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 86 158 2 24 43 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 86 158
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 86 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 86 158 2 23 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 86 158 (Polychromatic418967fa.accept_13_6_8_2_1_1484 45 86 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 86 158 2 22 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 86 158 (accept_3_2 43 86 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 86 158 2 21 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 86 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 86 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 158 2 20 43 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 158
  (Polychromatic418967fa.accept_19_1_10_6_1_5726 39 86 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 86 158 2 19 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 86 158 (accept_3_2 37 86 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86
  158 2 18 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  86 158 (Polychromatic418967fa.accept_11_2_9_4_1_310 35 86 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 86 158 2 17 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 86 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 86 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 86 158 2 16 43 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 86 158 (accept_3_2 31 86 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86 158 2 15 43 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 86 158
  (Polychromatic418967fa.accept_25_4_11_8_1_8657 29 86 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 86 158 2 14 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 86 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 86 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 86 158 2 13 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 86 158 (accept_3_2 25 86 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86 158 2 12 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 86 158 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 86 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 158 2 11 43 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 158
  (Polychromatic418967fa.accept_17_4_1_5_1_2554 21 86 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 86 158 2 10 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 86 158 (accept_3_2 19 86 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86
  158 2 9 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  86 158 (Polychromatic418967fa.accept_21_17_2_11_1_8656 17 86 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 86 158 2 8 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 86 158 (Polychromatic418967fa.accept_19_15_10_6_1_7169 15 86 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 158 2 7 43 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 158 (accept_3_2 13 86 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86 158 2 6 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 86 158 (Polychromatic418967fa.accept_27_11_5_23_1_8655 11 86
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 86 158 2 5 43 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 86 158
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 86 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 86 158 2 4 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 86 158 (accept_3_2 7 86 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 158
  2 3 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 86
  158 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 86 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 86 158 2 2 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 86 158 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 86 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 158 2 1 43 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 158 (accept_3_2 1 86 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 86 158))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74
  85 158 (Eq.refl Bool.true) (allA_of_3_0 74 85 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 84 158
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 84 158 2 37 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 84 158 (accept_3_2 73 84 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 158 2 36 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 84 158 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 84 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 158 2 35 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 69
  84 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 158 2 34 42 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 158 (accept_3_2 67
  84 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 158 2 33 42 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 84 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 158 2 32 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 84 158 (Polychromatic418967fa.accept_11_8_7_4_1_3011 63 84 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 158 2 31 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 158 (accept_3_2 61 84 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 158 2 30 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 158 (Polychromatic418967fa.accept_10_9_4_8_1_741 59 84 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 158 2 29 42 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 158
  (Polychromatic418967fa.accept_16_9_4_14_1_1878 57 84 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 84 158 2 28 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 84 158 (accept_3_2 55 84 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84
  158 2 27 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  84 158 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 84 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 84 158 2 26 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 84 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 84 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 158 2 25 42 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 158 (accept_3_2 49 84 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 158 2 24 42 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 84 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 158 2 23 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 84 158 (Polychromatic418967fa.accept_17_11_16_5_1_3612 45 84 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 158 2 22 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 158 (accept_3_2 43 84 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 158 2 21 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 158 (Polychromatic418967fa.accept_11_8_7_4_1_3011 41 84 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 158 2 20 42 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 158
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 84 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 84 158 2 19 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 84 158 (accept_3_2 37 84 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84
  158 2 18 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  84 158 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 84 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 84 158 2 17 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 84 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 84 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 158 2 16 42 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 158 (accept_3_2 31 84 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 158 2 15 42 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 84 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 158 2 14 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 84 158 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 84 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 158 2 13 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 158 (accept_3_2 25 84 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 158 2 12 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 158 (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 84 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 158 2 11 42 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 158
  (Polychromatic418967fa.accept_13_8_6_2_1_865 21 84 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 158 2 10 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 158 (accept_3_2 19 84 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84
  158 2 9 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  84 158 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 84 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 84 158 2 8 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 84 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 84 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 158 2 7 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 158 (accept_3_2 13 84 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 158 2 6 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 84 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 84 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 158 2 5 42 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 158
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 84 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 158 2 4 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 158 (accept_3_2 7 84 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 158
  2 3 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84
  158 (Polychromatic418967fa.accept_22_5_18_4_1_327 5 84 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 84 158 2 2 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 84 158 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 84 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 158 2 1 42 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 158 (accept_3_2 1 84 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 84 158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 76 83 158 (Eq.refl Bool.true) (allA_succ_of_accept 75 83 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 75
  83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 83 158
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 74 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 83 158 (accept_3_2 73 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  83 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 83 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 83 158 (accept_3_2 70 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 83 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 83 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 83 158
  (Polychromatic418967fa.accept_7_5_6_4_1_117 68 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 83 158 (accept_3_2 67 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  83 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 83 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 83 158 (accept_3_2 64 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 83 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 83 158
  (Polychromatic418967fa.accept_9_8_2_5_1_237 62 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 83 158 (accept_3_2 61 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  83 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 83 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 83 158 (accept_3_2 58 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 83 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 83 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 83 158
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 83 158 (accept_3_2 55 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  83 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 83 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 83 158 (accept_3_2 52 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 83 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 83 158
  (Polychromatic418967fa.accept_21_8_20_11_1_7025 50 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 83 158 (accept_3_2 49 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  83 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 83 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 83 158 (accept_3_2 46 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 83 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 83 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 83 158
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 83 158 (accept_3_2 43 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  83 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 83 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 83 158 (accept_3_2 40 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 83 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 83 158
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 83 158 (accept_3_2 37 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  83 158 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 83 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 83 158 (accept_3_2 34 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 83 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 83 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 83 158
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 83 158 (accept_3_2 31 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  83 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 83 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 83 158 (accept_3_2 28 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 83 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 158
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 83 158 (accept_3_2 25 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  83 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 83 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 158 (accept_3_2 22 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 83 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 83 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 158
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 83 158 (accept_3_2 19 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  83 158 (Polychromatic418967fa.accept_19_18_7_6_1_4367 18 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 83 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 158 (accept_3_2 16 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 158
  (Polychromatic418967fa.accept_19_14_7_6_1_8654 14 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 158 (accept_3_2 13 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 158 (Polychromatic418967fa.accept_10_1_3_8_1_136 11 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 158 (accept_3_2 10 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 158
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 158 (accept_3_2 7 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  158 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 83 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 83 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 158 (accept_3_2 4 83 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 83 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 83
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 158 (accept_3_2 1 83 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 82 158 (Eq.refl
  Bool.true) (allA_of_3_0 77 82 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 81 158 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 81 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 81 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 158 (accept_3_2 76 81 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 81 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 81 158 (Polychromatic418967fa.accept_13_9_3_2_1_399
  74 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 158 (accept_3_2 73
  81 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 81 158
  (Polychromatic418967fa.accept_19_15_5_6_1_5760 72 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 81 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 81 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 158 (accept_3_2 70 81 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 81 158 (Polychromatic418967fa.accept_10_9_1_8_1_755 69 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 158 (Polychromatic418967fa.accept_16_4_1_14_1_3908
  68 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 158 (accept_3_2 67
  81 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 81 158
  (Polychromatic418967fa.accept_12_6_9_2_1_311 66 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 81 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 81 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 158 (accept_3_2 64 81 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 81 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 158 (Polychromatic418967fa.accept_13_10_3_2_1_4728
  62 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 158 (accept_3_2 61
  81 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 158
  (Polychromatic418967fa.accept_17_9_13_5_1_3512 60 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 81 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 81 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 158 (accept_3_2 58 81 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 81 158 (Polychromatic418967fa.accept_13_5_3_2_1_1499 57 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 158 (Polychromatic418967fa.accept_19_18_5_6_1_2004
  56 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 158 (accept_3_2 55
  81 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 158
  (Polychromatic418967fa.accept_12_6_9_2_1_311 54 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 81 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 158 (accept_3_2 52 81 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 81 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 158 (Polychromatic418967fa.accept_13_11_3_2_1_863
  50 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 158 (accept_3_2 49
  81 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 158
  (Polychromatic418967fa.accept_13_9_3_2_1_399 48 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 81 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 81 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 158 (accept_3_2 46 81 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 81 158 (Polychromatic418967fa.accept_16_13_1_14_1_2855 45 81 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 158
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 44 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 158 (accept_3_2 43 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 158 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 158 (accept_3_2 40 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 158
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 38 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 158 (accept_3_2 37 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 158 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 158 (accept_3_2 34 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 158 (Polychromatic418967fa.accept_10_3_1_8_1_132 33 81 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 158
  (Polychromatic418967fa.accept_15_2_6_8_1_754 32 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 158 (accept_3_2 31 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 158 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 158 (accept_3_2 28 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 158
  (Polychromatic418967fa.accept_17_9_13_5_1_3512 26 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 158 (accept_3_2 25 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 158 (Polychromatic418967fa.accept_13_11_3_2_1_863 24 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 158 (accept_3_2 22 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 158 (Polychromatic418967fa.accept_14_7_11_4_1_3455 21 81 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 158
  (Polychromatic418967fa.accept_16_4_1_14_1_3908 20 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 158 (accept_3_2 19 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 158 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 158 (accept_3_2 16 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 158
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 14 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 158 (accept_3_2 13 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 158 (Polychromatic418967fa.accept_13_12_3_2_1_1470 12 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 158 (accept_3_2 10 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 158 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 81 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 158
  (Polychromatic418967fa.accept_14_8_11_4_1_3438 8 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 158 (accept_3_2 7 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  158 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 158 (accept_3_2 4 81 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 158 (Polychromatic418967fa.accept_15_2_6_8_1_754 2
  81 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 158 (accept_3_2 1 81 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 80 158 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 80 158 2 39 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 80 158 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 80 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 80 158 2 38 40 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 80 158
  (Polychromatic418967fa.accept_9_3_8_5_1_65 75 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 80 158 2 37 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 80 158 (accept_3_2 73 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 80
  158 2 36 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71
  80 158 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 80 158 2 35 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 80 158 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 80 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 158 2 34 40 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 158 (accept_3_2 67 80 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 158 2 33 40 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 158
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 80 158 2 32 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 80 158 (Polychromatic418967fa.accept_14_7_10_4_1_130 63 80 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 80 158 2 31 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 80 158 (accept_3_2 61 80 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80 158 2 30 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 80 158 (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 80 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 158 2 29 40 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 158
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 80 158 2 28 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 80 158 (accept_3_2 55 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80
  158 2 27 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  80 158 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 80 158 2 26 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 80 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 80 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 158 2 25 40 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 158 (accept_3_2 49 80 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 158 2 24 40 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 158
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 80 158 2 23 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 80 158 (Polychromatic418967fa.accept_23_22_11_20_1_8653 45 80 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 80 158 2 22 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 80 158 (accept_3_2 43 80 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80 158 2 21 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 80 158 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 80 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 80 158 2 20 40 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 80 158
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 80 158 2 19 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 80 158 (accept_3_2 37 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80
  158 2 18 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  80 158 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 80 158 2 17 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 80 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 80 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 80 158 2 16 40 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 80 158 (accept_3_2 31 80 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 158 2 15 40 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 158
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 80 158 2 14 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 80 158 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 80 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 158 2 13 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 158 (accept_3_2 25 80 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 158 2 12 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 158 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 80 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 158 2 11 40 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 158
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 158 2 10 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 158 (accept_3_2 19 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  158 2 9 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 158 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 158 2 8 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 158 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 80 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 158 2 7 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 158 (accept_3_2 13 80 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 158 2 6 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 80 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 80 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 158 2 5 40 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 158
  (Polychromatic418967fa.accept_17_9_12_5_1_219 9 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 158 2 4 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 158 (accept_3_2 7 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 158
  2 3 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  158 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 80 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 80 158 2 2 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 80 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 80 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 158 2 1 40 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 158 (accept_3_2 1 80 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 158))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  79 158 (allA_of_3_0 79 79 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 158 (allA_succ_of_accept 77 78
  158 (Polychromatic418967fa.accept_19_1_2_6_1_4411 77 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 78 158 2 38 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 78 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 78 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 158 2 37 39 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 158 (accept_3_2 73 78 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 158 2 36 39 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 158
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 78 158 2 35 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 78 158 (Polychromatic418967fa.accept_12_9_6_2_1_1273 69 78 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 78 158 2 34 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 78 158 (accept_3_2 67 78 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 158 2 33 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 78 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 158 2 32 39 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 158
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 78 158 2 31 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 78 158 (accept_3_2 61 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 78
  158 2 30 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  78 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 78 158 2 29 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 78 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 78 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 78 158 2 28 39 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 158 (accept_3_2 55 78 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 158 2 27 39 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 158
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 78 158 2 26 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 78 158 (Polychromatic418967fa.accept_12_3_6_2_1_747 51 78 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 158 2 25 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 158 (accept_3_2 49 78 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 158 2 24 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 78 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 158 2 23 39 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 158
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 158 2 22 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 78 158 (accept_3_2 43 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78
  158 2 21 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  78 158 (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 78 158 2 20 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 78 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 78 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 158 2 19 39 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 158 (accept_3_2 37 78 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 158 2 18 39 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 158
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 78 158 2 17 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 78 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 78 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 158 2 16 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 158 (accept_3_2 31 78 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 158 2 15 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 78 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 158 2 14 39 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 158
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 158 2 13 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 78 158 (accept_3_2 25 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78
  158 2 12 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  78 158 (Polychromatic418967fa.accept_19_4_2_6_1_7181 23 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 78 158 2 11 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 78 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 78 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 158 2 10 39 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 158 (accept_3_2 19 78 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 158 2 9 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 17
  78 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 158 2 8 39 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 158
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 78 158 2 7 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 78 158 (accept_3_2 13 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78
  158 2 6 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  78 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 78 158 2 5 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 78 158 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 78 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 158 2 4 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 158 (accept_3_2 7 78 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 158 2 3 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 78 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 78 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 158 2 2 39 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 158
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 78 158 2 1 39 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 158 (accept_3_2 1 78 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 158
  (allA_succ_of_accept 76 77 158 (accept_3_2 76 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 158 (Polychromatic418967fa.accept_16_10_13_14_1_5042 74 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 158 (accept_3_2 73 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 158 (Polychromatic418967fa.accept_22_6_11_4_1_8652 72 77
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 158 (accept_3_2 70 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 68 77 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 158 (accept_3_2 67 77 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 158 (Polychromatic418967fa.accept_13_1_12_2_1_384 66 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 158
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 65 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 158 (accept_3_2 64 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 158 (Polychromatic418967fa.accept_13_10_12_2_1_1460 62 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 158 (accept_3_2 61 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 158 (Polychromatic418967fa.accept_19_3_1_6_1_3114 60 77 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 158 (accept_3_2 58 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 77 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 158 (accept_3_2 55 77 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 158 (Polychromatic418967fa.accept_15_9_2_8_1_1379 54 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 158
  (Polychromatic418967fa.accept_13_1_12_2_1_384 53 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 158 (accept_3_2 52 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 158 (Polychromatic418967fa.accept_20_10_17_18_1_7120 50 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 158 (accept_3_2 49 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 158 (Polychromatic418967fa.accept_17_14_9_5_1_4755 48 77
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 158 (accept_3_2 46 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 77 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 158 (accept_3_2 43 77 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 158 (Polychromatic418967fa.accept_13_3_12_2_1_385 42 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 158
  (Polychromatic418967fa.accept_17_7_9_5_1_2588 41 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 158 (accept_3_2 40 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 158 (Polychromatic418967fa.accept_14_10_7_4_1_3453 38 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 158 (accept_3_2 37 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 158 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 77
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 158 (accept_3_2 34 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 77 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 158 (accept_3_2 31 77 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 158 (Polychromatic418967fa.accept_13_4_12_2_1_1459 30 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 158
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 158 (accept_3_2 28 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 158 (Polychromatic418967fa.accept_16_10_13_14_1_5042 26 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 158 (accept_3_2 25 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 158 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 77
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 158 (accept_3_2 22 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 77 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 158 (accept_3_2 19 77 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 158 (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 158
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 17 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 158 (accept_3_2 16 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 158 (Polychromatic418967fa.accept_13_1_12_2_1_384 14 77 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 158 (accept_3_2 13 77 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 158 (Polychromatic418967fa.accept_17_12_9_5_1_799 12 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 158 (accept_3_2 10 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 77 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 158 (accept_3_2 7 77 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 158 (Polychromatic418967fa.accept_13_6_12_2_1_4707 6 77 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 158
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 158 (accept_3_2 4 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 158 (Polychromatic418967fa.accept_19_2_1_6_1_5780 2 77 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 158 (accept_3_2 1 77 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 158))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 158 (allA_of_3_0 76 76 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 158 (allA_succ_of_accept 74 75
  158 (Polychromatic418967fa.accept_9_2_3_5_1_60 74 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 158 (accept_3_2 73 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 158 (accept_3_2 70 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 75 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 158
  (Polychromatic418967fa.accept_11_2_9_4_1_310 68 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 158 (accept_3_2 67 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 66 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 158 (accept_3_2 64 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 158 (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 75 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 158
  (Polychromatic418967fa.accept_7_6_5_4_1_297 62 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 158 (accept_3_2 61 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 158 (accept_3_2 58 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 75 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 158 (accept_3_2 55 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 158 (accept_3_2 52 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 75 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 158
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 158 (accept_3_2 49 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 158 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 158 (accept_3_2 46 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 75 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 158
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 158 (accept_3_2 43 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 158 (accept_3_2 40 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 158 (Polychromatic418967fa.accept_19_1_18_6_1_3110 39 75 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 158 (accept_3_2 37 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 158 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 158 (accept_3_2 34 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 158
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 158 (accept_3_2 31 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 158 (accept_3_2 28 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 158 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 75 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 158
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 158 (accept_3_2 25 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 158 (accept_3_2 22 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 158
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 158 (accept_3_2 19 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 158 (accept_3_2 16 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 158 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 75 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 158
  (Polychromatic418967fa.accept_21_14_12_11_1_3956 14 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 75 158 (accept_3_2 13 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 158 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 75 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 158 (accept_3_2 10 75 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 158
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 158 (accept_3_2 7 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  158 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 75 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 158 (accept_3_2 4 75 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 158 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 75 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  75 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 158 (accept_3_2 1 75 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  158))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 158 (allA_succ_of_accept
  73 74 158 (accept_3_2 73 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 158 2 36 37 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 158
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 158 2 35 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 74 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 74 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 158 2 34 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 158 (accept_3_2 67 74 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 158 2 33 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 158 (Polychromatic418967fa.accept_15_5_14_8_1_1376 65 74 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 158 2 32 37 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 158
  (Polychromatic418967fa.accept_13_11_9_2_1_2969 63 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 158 2 31 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 74 158 (accept_3_2 61 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 74
  158 2 30 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  74 158 (Polychromatic418967fa.accept_10_9_4_8_1_741 59 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 74 158 2 29 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 74 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 74 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 74 158 2 28 37 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 74 158 (accept_3_2 55 74 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 74 158 2 27 37 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 74 158
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 74 158 2 26 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 74 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 74 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 74 158 2 25 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 74 158 (accept_3_2 49 74 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74 158 2 24 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 74 158 (Polychromatic418967fa.accept_16_15_10_14_1_2872 47 74
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 158 2 23 37 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 158
  (Polychromatic418967fa.accept_11_1_8_4_1_717 45 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 158 2 22 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 74 158 (accept_3_2 43 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74
  158 2 21 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  74 158 (Polychromatic418967fa.accept_19_3_17_6_1_1991 41 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 74 158 2 20 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 74 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 74 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 74 158 2 19 37 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 74 158 (accept_3_2 37 74 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74 158 2 18 37 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 74 158
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 74 158 2 17 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 74 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 74 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 158 2 16 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 158 (accept_3_2 31 74 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 158 2 15 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 158 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 74 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 158 2 14 37 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 158
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 158 2 13 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 74 158 (accept_3_2 25 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74
  158 2 12 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  74 158 (Polychromatic418967fa.accept_11_1_8_4_1_717 23 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 74 158 2 11 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 74 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 74 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 158 2 10 37 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 158 (accept_3_2 19 74 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 158 2 9 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 74 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 17
  74 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 158 2 8 37 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 158
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 158 2 7 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 158 (accept_3_2 13 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74
  158 2 6 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  74 158 (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 158 2 5 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 158 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 74 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 158 2 4 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 158 (accept_3_2 7 74 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 158 2 3 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 74 158 (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 74 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 158 2 2 37 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 158
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 158 2 1 37 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 158 (accept_3_2 1 74 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 158 (allA_of_3_0 73 73 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 158 (allA_succ_of_accept 71 72 158
  (Polychromatic418967fa.accept_15_11_12_8_1_739 71 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 72 158 2 35 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 72 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 72 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 158 2 34 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 158 (accept_3_2 67 72 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 158 2 33 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 158 (Polychromatic418967fa.accept_10_5_2_8_1_135 65 72 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 158 2 32 36 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 158
  (Polychromatic418967fa.accept_15_3_12_8_1_738 63 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 72 158 2 31 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 72 158 (accept_3_2 61 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72
  158 2 30 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  72 158 (Polychromatic418967fa.accept_19_2_15_6_1_4408 59 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 72 158 2 29 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 72 158 (Polychromatic418967fa.accept_11_2_6_4_1_3028 57 72 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 158 2 28 36 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 158 (accept_3_2 55 72 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 158 2 27 36 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 158
  (Polychromatic418967fa.accept_22_9_6_4_1_5347 53 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 72 158 2 26 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 72 158 (Polychromatic418967fa.accept_14_9_2_4_1_1814 51 72 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 158 2 25 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 158 (accept_3_2 49 72 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 158 2 24 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 72 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 158 2 23 36 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 158
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 158 2 22 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 158 (accept_3_2 43 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72
  158 2 21 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  72 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 72 158 2 20 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 72 158 (Polychromatic418967fa.accept_21_18_9_11_1_7082 39 72 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 158 2 19 36 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 158 (accept_3_2 37 72 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 158 2 18 36 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 158
  (Polychromatic418967fa.accept_10_5_2_8_1_135 35 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 72 158 2 17 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 72 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 72 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 72 158 2 16 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 158 (accept_3_2 31 72 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 158 2 15 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 158 (Polychromatic418967fa.accept_19_10_15_6_1_5772 29 72
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 158 2 14 36 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 158
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 72 158 2 13 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 72 158 (accept_3_2 25 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72
  158 2 12 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  72 158 (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 72 158 2 11 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 72 158 (Polychromatic418967fa.accept_13_8_7_2_1_2988 21 72 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 72 158 2 10 36 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 158 (accept_3_2 19 72 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 158 2 9 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 158 (Polychromatic418967fa.accept_22_17_6_4_1_8651
  17 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 158 2 8 36 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72 158
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 72 158 2 7 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 72 158 (accept_3_2 13 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72
  158 2 6 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  72 158 (Polychromatic418967fa.accept_15_11_12_8_1_739 11 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 72 158 2 5 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 72 158 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 72 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 158 2 4 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 158 (accept_3_2 7 72 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 158 2 3 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 72 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 72 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 158 2 2 36 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72 158
  (Polychromatic418967fa.accept_15_3_12_8_1_738 3 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 72 158 2 1 36 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 72 158 (accept_3_2 1 72 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 158 (allA_succ_of_accept 70
  71 158 (accept_3_2 70 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 71 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 71 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 71 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 158 (accept_3_2 67 71 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 71 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 65
  71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 158 (accept_3_2 64 71
  158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 158 (Polychromatic418967fa.accept_6_3_5_2_1_12
  63 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 71 158
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 62 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 71 158 (accept_3_2 61 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  71 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 71 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 71 158 (accept_3_2 58 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 71 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 71 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 71 158
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 71 158 (accept_3_2 55 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  71 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 71 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 158 (accept_3_2 52 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 71 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 158
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 50 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 71 158 (accept_3_2 49 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  71 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 71 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 158 (accept_3_2 46 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 71 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 158
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 71 158 (accept_3_2 43 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 158 (accept_3_2 40 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 158
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 158 (accept_3_2 37 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 158 (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 158 (Polychromatic418967fa.accept_13_9_6_2_1_2200 35 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 158 (accept_3_2 34 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 71 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 158
  (Polychromatic418967fa.accept_11_10_5_4_1_711 32 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 158 (accept_3_2 31 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 158 (accept_3_2 28 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 158
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 158 (accept_3_2 25 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 158 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 158 (accept_3_2 22 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 158
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 158 (accept_3_2 19 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 158 (Polychromatic418967fa.accept_15_3_11_8_1_4186 18 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 158 (accept_3_2 16 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 158
  (Polychromatic418967fa.accept_13_1_6_2_1_377 14 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 158 (accept_3_2 13 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 158 (accept_3_2 10 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 158
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 158 (accept_3_2 7 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  158 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 158 (accept_3_2 4 71 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  71 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 158 (accept_3_2 1 71 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  158))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 158 (allA_of_3_0 70 70 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 158 (allA_succ_of_accept 68 69 158
  (Polychromatic418967fa.accept_7_5_6_4_1_117 68 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 158 (accept_3_2 67 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 158 (accept_3_2 64 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 69 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 158
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 158 (accept_3_2 61 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 158 (Polychromatic418967fa.accept_21_18_6_11_1_7031 60 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 158 (accept_3_2 58 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 69 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 158
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 158 (accept_3_2 55 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 158 (accept_3_2 52 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 69 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 158
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 50 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 158 (accept_3_2 49 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 158 (accept_3_2 46 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 69 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 158
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 158 (accept_3_2 43 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 158 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 158 (accept_3_2 40 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 158
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 158 (accept_3_2 37 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 158 (Polychromatic418967fa.accept_19_17_12_6_1_8650 36 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 158 (accept_3_2 34 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 69 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 158
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 32 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 158 (accept_3_2 31 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 158 (accept_3_2 28 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 158
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 158 (accept_3_2 25 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 158 (accept_3_2 22 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 158
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 158 (accept_3_2 19 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 158 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 158 (accept_3_2 16 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 158
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 158 (accept_3_2 13 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 158 (accept_3_2 10 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 69 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 158
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 158 (accept_3_2 7 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  158 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 69 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 158 (accept_3_2 4 69 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 69
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 158 (accept_3_2 1 69 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  158))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 158 (allA_succ_of_accept 67 68
  158 (accept_3_2 67 68 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 158 2 33 34 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 158
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 68 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 158 2 32 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 68 158 (Polychromatic418967fa.accept_13_11_3_2_1_863 63 68 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 158 2 31 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 158 (accept_3_2 61 68 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 158 2 30 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 158 (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 68 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 158 2 29 34 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 158
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 68 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 158 2 28 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 158 (accept_3_2 55 68 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68
  158 2 27 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  68 158 (Polychromatic418967fa.accept_11_9_2_4_1_707 53 68 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 68 158 2 26 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 68 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 68 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 158 2 25 34 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 158 (accept_3_2 49 68 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 158 2 24 34 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 158
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 68 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 68 158 2 23 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 68 158 (Polychromatic418967fa.accept_27_18_14_23_1_8649 45 68 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 158 2 22 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 158 (accept_3_2 43 68 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 158 2 21 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 158 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 68 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 158 2 20 34 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 158
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 68 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 158 2 19 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 68 158 (accept_3_2 37 68 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68
  158 2 18 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  68 158 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 68 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 68 158 2 17 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 68 158 (Polychromatic418967fa.accept_16_1_4_14_1_1896 33 68 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 68 158 2 16 34 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 68 158 (accept_3_2 31 68 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68 158 2 15 34 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 68 158
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 68 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 68 158 2 14 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 68 158 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 68 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 158 2 13 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 158 (accept_3_2 25 68 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 158 2 12 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 68 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 158 2 11 34 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 158
  (Polychromatic418967fa.accept_20_1_8_18_1_8648 21 68 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 158 2 10 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 158 (accept_3_2 19 68 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  158 2 9 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 158 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 68 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 158 2 8 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 158 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 68 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 158 2 7 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 158 (accept_3_2 13 68 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 158 2 6 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 68 158 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 68 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 158 2 5 34 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 158
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 68 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 158 2 4 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 158 (accept_3_2 7 68 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 158
  2 3 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  158 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 68 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 68 158 2 2 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 68 158 (Polychromatic418967fa.accept_20_3_8_18_1_5603 3 68 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 158 2 1 34 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 158 (accept_3_2 1 68 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 158
  (allA_of_3_0 67 67 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 158 (allA_succ_of_accept 65 66 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 66 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 158 2 32 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 66 158 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 66 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 158 2 31 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 158 (accept_3_2 61 66 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 158 2 30 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 158 (Polychromatic418967fa.accept_15_14_6_8_1_1410 59 66 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 158 2 29 33 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 158
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 66 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 158 2 28 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 66 158 (accept_3_2 55 66 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66
  158 2 27 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  66 158 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 66 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 66 158 2 26 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 66 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 66 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 158 2 25 33 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 158 (accept_3_2 49 66 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 158 2 24 33 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 66 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 158 2 23 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 66 158 (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 66 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 158 2 22 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 158 (accept_3_2 43 66 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 158 2 21 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 158 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 66 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 158 2 20 33 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 158
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 66 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 158 2 19 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 66 158 (accept_3_2 37 66 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66
  158 2 18 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  66 158 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 66 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 66 158 2 17 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 66 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 66 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 158 2 16 33 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 158 (accept_3_2 31 66 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 158 2 15 33 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 158
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 66 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 158 2 14 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 66 158 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 66 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 158 2 13 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 158 (accept_3_2 25 66 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 158 2 12 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 158 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 66 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 158 2 11 33 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 158
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 66 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 158 2 10 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 66 158 (accept_3_2 19 66 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66
  158 2 9 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  66 158 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 66 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 66 158 2 8 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 66 158 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 66 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 158 2 7 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 158 (accept_3_2 13 66 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 158 2 6 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 66 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 66 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 158 2 5 33 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 158
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 66 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 158 2 4 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 158 (accept_3_2 7 66 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 158
  2 3 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66
  158 (Polychromatic418967fa.accept_25_5_16_8_1_8647 5 66 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 66 158 2 2 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 66 158 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 66 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 158 2 1 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 158 (accept_3_2 1 66 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 66 158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65
  158 (allA_succ_of_accept 64 65 158 (accept_3_2 64 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 65 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 65 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 158 (accept_3_2 61 65 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 65 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 158 (accept_3_2 58 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 65 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 158 (accept_3_2 55 65 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 65 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 158
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 158 (accept_3_2 52 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 158 (Polychromatic418967fa.accept_19_12_8_6_1_8646 50 65 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 158 (accept_3_2 49 65 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 65 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 158 (accept_3_2 46 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 65 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 158 (accept_3_2 43 65 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 65 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 158
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 158 (accept_3_2 40 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 158 (Polychromatic418967fa.accept_11_5_10_4_1_1157 38 65 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 158 (accept_3_2 37 65 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 158 (Polychromatic418967fa.accept_16_4_1_14_1_3908 36 65
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 158 (accept_3_2 34 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 158 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 65 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 158 (accept_3_2 31 65 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 65 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 158
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 158 (accept_3_2 28 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 65 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 158 (accept_3_2 25 65 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 65 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 158 (accept_3_2 22 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 65 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 158 (accept_3_2 19 65 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 158 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 65 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 158
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 158 (accept_3_2 16 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 158 (Polychromatic418967fa.accept_15_14_5_8_1_3175 14 65 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 158 (accept_3_2 13 65 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 65 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 158 (accept_3_2 10 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 65 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 158 (accept_3_2 7 65 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 65 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 158
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 158 (accept_3_2 4 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 158 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 65 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 158 (accept_3_2 1 65 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 158))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 158
  (allA_of_3_0 64 64 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 158 (allA_succ_of_accept 62 63 158
  (Polychromatic418967fa.accept_11_7_8_4_1_718 62 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 158 (accept_3_2 61 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 158 (Polychromatic418967fa.accept_17_9_12_5_1_219 60 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 158 (accept_3_2 58 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 63 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 158
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 158 (accept_3_2 55 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 158 (accept_3_2 52 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 158 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 63 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 158
  (Polychromatic418967fa.accept_15_5_3_8_1_748 50 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 158 (accept_3_2 49 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 158 (Polychromatic418967fa.accept_13_9_11_2_1_1491 48 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 158 (accept_3_2 46 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 158
  (Polychromatic418967fa.accept_17_10_12_5_1_6028 44 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 158 (accept_3_2 43 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 158 (accept_3_2 40 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 158 (Polychromatic418967fa.accept_14_11_7_4_1_3449 39 63 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 158
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 38 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 158 (accept_3_2 37 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 158 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 158 (accept_3_2 34 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 158
  (Polychromatic418967fa.accept_27_5_9_23_1_6576 32 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 158 (accept_3_2 31 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 158 (accept_3_2 28 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 158 (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 63 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 158
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 158 (accept_3_2 25 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 158 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 158 (accept_3_2 22 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 158
  (Polychromatic418967fa.accept_15_5_3_8_1_748 20 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 158 (accept_3_2 19 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 158 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 158 (accept_3_2 16 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 158 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 63 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 158
  (Polychromatic418967fa.accept_23_14_17_20_1_8624 14 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 63 158 (accept_3_2 13 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 63 158 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 63 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 158 (accept_3_2 10 63 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 158
  (Polychromatic418967fa.accept_17_8_12_5_1_1577 8 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 158 (accept_3_2 7 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  158 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 63 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 158 (accept_3_2 4 63 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 158 (Polychromatic418967fa.accept_13_3_11_2_1_1422 3 63 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 158
  (Polychromatic418967fa.accept_20_2_3_18_1_8645 2 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 158 (accept_3_2 1 63 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  158))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 158 (allA_succ_of_accept 61 62 158
  (accept_3_2 61 62 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 158 2 30 31 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 158
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 62 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 158 2 29 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 62 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 62 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 158 2 28 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 158 (accept_3_2 55 62 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 158 2 27 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 158 (Polychromatic418967fa.accept_19_15_5_6_1_5760 53 62 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 158 2 26 31 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 158
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 62 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 158 2 25 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 62 158 (accept_3_2 49 62 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62
  158 2 24 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  62 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 62 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 62 158 2 23 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 62 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 62 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 158 2 22 31 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 158 (accept_3_2 43 62 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 158 2 21 31 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 158
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 41 62 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 62 158 2 20 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 62 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 158 2 19 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 158 (accept_3_2 37 62 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 158 2 18 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 158 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 62 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 158 2 17 31 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 158
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 62 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 158 2 16 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 62 158 (accept_3_2 31 62 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62
  158 2 15 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  62 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 62 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 62 158 2 14 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 62 158 (Polychromatic418967fa.accept_20_7_2_18_1_5618 27 62 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 158 2 13 31 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 158 (accept_3_2 25 62 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 158 2 12 31 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 158
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 62 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 158 2 11 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 62 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 158 2 10 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 158 (accept_3_2 19 62 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 158 2 9 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 62 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 158 2 8 31 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 158
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 62 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 158 2 7 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 158 (accept_3_2 13 62 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  158 2 6 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 62 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 158 2 5 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 62 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 158 2 4 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 158 (accept_3_2 7 62 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 158 2 3 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 62 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 158 2 2 31 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 158
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 62 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 158 2 1 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 158 (accept_3_2 1 62 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 158 (allA_of_3_0 61 61 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 158 (allA_succ_of_accept 59 60 158
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 59 60 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 158 2 29 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 60 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 158 2 28 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 158 (accept_3_2 55 60 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 158 2 27 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 158 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 60 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 158 2 26 30 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 158
  (Polychromatic418967fa.accept_21_9_18_11_1_8644 51 60 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 158 2 25 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 158 (accept_3_2 49 60 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60
  158 2 24 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  60 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 60 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 60 158 2 23 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 60 158 (Polychromatic418967fa.accept_13_6_8_2_1_1484 45 60 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 158 2 22 30 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 158 (accept_3_2 43 60 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 158 2 21 30 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 158
  (Polychromatic418967fa.accept_17_7_9_5_1_2588 41 60 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 158 2 20 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 60 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 60 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 158 2 19 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 158 (accept_3_2 37 60 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 158 2 18 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 158 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 60 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 158 2 17 30 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 158
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 60 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 158 2 16 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 158 (accept_3_2 31 60 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  158 2 15 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 60 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 158 2 14 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 60 158 (Polychromatic418967fa.accept_18_9_6_14_1_5913 27 60 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 158 2 13 30 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 158 (accept_3_2 25 60 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 158 2 12 30 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 158
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 23 60 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 60 158 2 11 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 60 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 60 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 158 2 10 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 158 (accept_3_2 19 60 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 158 2 9 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 60 158 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 60 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 158 2 8 30 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 60 158
  (Polychromatic418967fa.accept_22_15_16_4_1_8643 15 60 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 60 158 2 7 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 60 158 (accept_3_2 13 60 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60
  158 2 6 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  60 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 60 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 60 158 2 5 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 60 158 (Polychromatic418967fa.accept_18_9_6_14_1_5913 9 60 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 158 2 4 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 158 (accept_3_2 7 60 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 158 2 3 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 60 158 (Polychromatic418967fa.accept_19_5_3_6_1_8642 5 60 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 158 2 2 30 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 158
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 60 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 158 2 1 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 158 (accept_3_2 1 60 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 158 (allA_succ_of_accept 58 59 158
  (accept_3_2 58 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 158 (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 59 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 158 (accept_3_2 55 59 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 158 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 59 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 53
  59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 158 (accept_3_2 52 59
  158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 158 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 158
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 158 (accept_3_2 49 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 158 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 158 (Polychromatic418967fa.accept_10_7_9_8_1_1135 47 59 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 158 (accept_3_2 46 59 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 59 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 158
  (Polychromatic418967fa.accept_10_4_9_8_1_125 44 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 158 (accept_3_2 43 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 158 (Polychromatic418967fa.accept_19_4_2_6_1_7181 42 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 59 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 158 (accept_3_2 40 59 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 158
  (Polychromatic418967fa.accept_22_16_15_4_1_8641 38 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 158 (accept_3_2 37 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 158 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 158 (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 59 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 158 (accept_3_2 34 59 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 158
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 158 (accept_3_2 31 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 158 (Polychromatic418967fa.accept_17_13_8_5_1_3532 30 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 158 (accept_3_2 28 59 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 158
  (Polychromatic418967fa.accept_18_8_5_14_1_3353 26 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 158 (accept_3_2 25 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 158 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 158 (Polychromatic418967fa.accept_19_4_2_6_1_7181 23 59 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 158 (accept_3_2 22 59 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 158
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 158 (accept_3_2 19 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 158 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 158 (accept_3_2 16 59 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 158
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 158 (accept_3_2 13 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 158 (Polychromatic418967fa.accept_17_12_8_5_1_6018 12 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 158 (Polychromatic418967fa.accept_10_1_9_8_1_123 11 59 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 158 (accept_3_2 10 59 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 158
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 158 (accept_3_2 7 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  158 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 158 (accept_3_2 4 59 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 158 (Polychromatic418967fa.accept_21_2_17_11_1_7037
  2 59 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 158 (accept_3_2 1 59
  158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  158))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 158 (allA_of_3_0 58 58 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 57 158 (allA_succ_of_accept 56 57 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 158 (accept_3_2 55 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 158 (accept_3_2 52 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 57 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 158
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 50 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 158 (accept_3_2 49 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 158 (Polychromatic418967fa.accept_13_9_5_2_1_2185 48 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 158 (accept_3_2 46 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 57 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 158
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 158 (accept_3_2 43 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 158 (accept_3_2 40 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 158
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 158 (accept_3_2 37 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 158 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 158 (accept_3_2 34 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 57 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 158
  (Polychromatic418967fa.accept_23_9_11_20_1_6940 32 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 158 (accept_3_2 31 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 158 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 158 (accept_3_2 28 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 158
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 158 (accept_3_2 25 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 158 (accept_3_2 22 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 158 (Polychromatic418967fa.accept_16_5_9_14_1_5051 21 57 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 158 (accept_3_2 19 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 158 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 158 (accept_3_2 16 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 158
  (Polychromatic418967fa.accept_22_14_13_4_1_8640 14 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 158 (accept_3_2 13 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 158 (accept_3_2 10 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 158 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 57 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 158
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 158 (accept_3_2 7 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  158 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 57 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 158 (accept_3_2 4 57 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 57
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 158 (accept_3_2 1 57 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 158)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 158 (allA_succ_of_accept 55 56 158 (accept_3_2 55 56 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 158 2 27 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 56 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 158 2 26 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 51
  56 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 158 2 25 28 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 158 (accept_3_2 49
  56 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 158 2 24 28 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 158
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 56 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 158 2 23 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 158 (Polychromatic418967fa.accept_13_6_4_2_1_1433 45 56 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 158 2 22 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 158 (accept_3_2 43 56 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 158 2 21 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 158 (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 56 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 158 2 20 28 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 158
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 56 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 158 2 19 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 158 (accept_3_2 37 56 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  158 2 18 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  56 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 56 158 2 17 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 56 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 56 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 158 2 16 28 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 158 (accept_3_2 31 56 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 158 2 15 28 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 158
  (Polychromatic418967fa.accept_12_5_8_2_1_309 29 56 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 56 158 2 14 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 56 158 (Polychromatic418967fa.accept_15_12_11_8_1_1392 27 56 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 158 2 13 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 158 (accept_3_2 25 56 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 158 2 12 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 158 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 56 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 158 2 11 28 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 158
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 56 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 158 2 10 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 158 (accept_3_2 19 56 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  158 2 9 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 158 2 8 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 56 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 158 2 7 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 158 (accept_3_2 13 56 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 158 2 6 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 56 158 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 56 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 158 2 5 28 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 158
  (Polychromatic418967fa.accept_19_9_18_6_1_5778 9 56 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 158 2 4 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 158 (accept_3_2 7 56 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 158
  2 3 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56
  158 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 56 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 158 2 2 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 56 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 158 2 1 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 158 (accept_3_2 1 56 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 158)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 158 (allA_of_3_0 55
  55 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 158 (allA_succ_of_accept 53 54 158
  (Polychromatic418967fa.accept_17_2_3_5_1_763 53 54 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 158 2 26 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 54 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 158 2 25 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 158 (accept_3_2 49 54 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 158 2 24 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 158 (Polychromatic418967fa.accept_15_2_9_8_1_736 47 54 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 158 2 23 27 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 158
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 54 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 158 2 22 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 158 (accept_3_2 43 54 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54
  158 2 21 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  54 158 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 54 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 54 158 2 20 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 54 158 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 54 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 158 2 19 27 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 158 (accept_3_2 37 54 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 158 2 18 27 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 158
  (Polychromatic418967fa.accept_21_14_12_11_1_3956 35 54 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 54 158 2 17 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 54 158 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 54 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 158 2 16 27 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 158 (accept_3_2 31 54 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 158 2 15 27 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 158
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 54 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 54 158 2 14 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 54 158 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 54 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 158 2 13 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 158 (accept_3_2 25 54 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 158 2 12 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 54 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 158 2 11 27 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 158
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 54 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 54 158 2 10 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 54 158 (accept_3_2 19 54 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54
  158 2 9 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  54 158 (Polychromatic418967fa.accept_15_2_9_8_1_736 17 54 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 54 158 2 8 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 54 158 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 54 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 158 2 7 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 158 (accept_3_2 13 54 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 158 2 6 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 54 158 (Polychromatic418967fa.accept_19_11_16_6_1_7155 11 54 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 158 2 5 27 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 54 158
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 54 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 54 158 2 4 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 54 158 (accept_3_2 7 54 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 158
  2 3 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54
  158 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 54 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 54 158 2 2 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 54 158 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 54 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 158 2 1 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 158 (accept_3_2 1 54 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 54 158)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 158
  (allA_succ_of_accept 52 53 158 (accept_3_2 52 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  53 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 158 (Polychromatic418967fa.accept_14_8_11_4_1_3438 50 53 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 158 (accept_3_2 49 53 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 53 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 158 (accept_3_2 46 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 53 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 158 (accept_3_2 43 53 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 53 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 158
  (Polychromatic418967fa.accept_10_1_3_8_1_136 41 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 158 (accept_3_2 40 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 53 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 158 (accept_3_2 37 53 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 158 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 53 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 158 (accept_3_2 34 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 53 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 158 (accept_3_2 31 53 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 53 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 158
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 158 (accept_3_2 28 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 158 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 53 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 158 (accept_3_2 25 53 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 53 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 158 (accept_3_2 22 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 53 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 158 (accept_3_2 19 53 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 158 (Polychromatic418967fa.accept_26_18_1_2_1_8639 18 53 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 158
  (Polychromatic418967fa.accept_22_17_9_4_1_8638 17 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 158 (accept_3_2 16 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 158 (Polychromatic418967fa.accept_17_14_2_5_1_3560 14 53 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 158 (accept_3_2 13 53 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 53 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 158 (accept_3_2 10 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 53 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 158 (accept_3_2 7 53 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 53 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 158
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 158 (accept_3_2 4 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 53 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 158 (accept_3_2 1 53 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 158))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 158 (allA_of_3_0 52 52
  158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 158 (allA_succ_of_accept 50 51 158
  (Polychromatic418967fa.accept_19_12_13_6_1_7130 50 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 158 (accept_3_2 49 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 158 (accept_3_2 46 51 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 51 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 158
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 158 (accept_3_2 43 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 158 (accept_3_2 40 51 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 51 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 158
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 158 (accept_3_2 37 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 158 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 158 (accept_3_2 34 51 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 158
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 32 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 158 (accept_3_2 31 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 158 (accept_3_2 28 51 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 51 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 158
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 158 (accept_3_2 25 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 158 (Polychromatic418967fa.accept_23_1_5_20_1_8637 24 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 158 (accept_3_2 22 51 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 158
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 158 (accept_3_2 19 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 158 (accept_3_2 16 51 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 158 (Polychromatic418967fa.accept_19_15_13_6_1_8636 15 51 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 158
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 158 (accept_3_2 13 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 158 (accept_3_2 10 51 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 158
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 158 (accept_3_2 7 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  158 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 158 (accept_3_2 4 51 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 51 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  51 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 158 (accept_3_2 1 51 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 158)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 158 (allA_succ_of_accept 49 50 158 (accept_3_2 49 50 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 158 2 24 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 50 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 50 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 158 2 23 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 50 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 45
  50 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 158 2 22 25 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 158 (accept_3_2 43
  50 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 158 2 21 25 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 158
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 41 50 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 158 2 20 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 158 (Polychromatic418967fa.accept_14_11_8_4_1_2628 39 50 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 158 2 19 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 158 (accept_3_2 37 50 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 158 2 18 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50 158 (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 50 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 158 2 17 25 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 158
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 50 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 158 2 16 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 50 158 (accept_3_2 31 50 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50
  158 2 15 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  50 158 (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 50 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 50 158 2 14 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 50 158 (Polychromatic418967fa.accept_15_12_5_8_1_5247 27 50 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 158 2 13 25 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 158 (accept_3_2 25 50 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 158 2 12 25 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 158
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 50 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 158 2 11 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 158 (Polychromatic418967fa.accept_17_4_16_5_1_8635 21 50 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 158 2 10 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 158 (accept_3_2 19 50 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 158 2 9 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 50 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 50 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 158 2 8 25 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 158
  (Polychromatic418967fa.accept_19_15_12_6_1_8634 15 50 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 50 158 2 7 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 50 158 (accept_3_2 13 50 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50
  158 2 6 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  50 158 (Polychromatic418967fa.accept_14_11_8_4_1_2628 11 50 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 50 158 2 5 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 50 158 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 50 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 158 2 4 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 158 (accept_3_2 7 50 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 158 2 3 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 50 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 50 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 158 2 2 25 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 158
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 50 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 158 2 1 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 158 (accept_3_2 1 50 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  158)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 158 (allA_of_3_0 49 49 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 48 158 (allA_succ_of_accept 47 48 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 47
  48 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 158 2 23 24 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 158
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 48 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 158 2 22 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 158 (accept_3_2 43 48 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48
  158 2 21 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  48 158 (Polychromatic418967fa.accept_15_11_3_8_1_750 41 48 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 48 158 2 20 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 48 158 (Polychromatic418967fa.accept_15_9_3_8_1_3155 39 48 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 158 2 19 24 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 158 (accept_3_2 37 48 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 158 2 18 24 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 158
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 48 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 158 2 17 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 48 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 48 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 158 2 16 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 158 (accept_3_2 31 48 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 158 2 15 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 48 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 158 2 14 24 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 158
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 48 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 48 158 2 13 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 48 158 (accept_3_2 25 48 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48
  158 2 12 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  48 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 48 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 48 158 2 11 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 48 158 (Polychromatic418967fa.accept_18_3_12_14_1_2232 21 48 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 158 2 10 24 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 158 (accept_3_2 19 48 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 158 2 9 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 17
  48 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 158 2 8 24 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48 158
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 48 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 48 158 2 7 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 48 158 (accept_3_2 13 48 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48
  158 2 6 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  48 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 48 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 48 158 2 5 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 48 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 48 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 158 2 4 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 158 (accept_3_2 7 48 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 158 2 3 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 48 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 48 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 158 2 2 24 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48 158
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 48 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 48 158 2 1 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 48 158 (accept_3_2 1 48 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  158)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 158 (allA_succ_of_accept 46 47 158 (accept_3_2 46 47
  158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 158 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 158
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 47 158 (accept_3_2 43 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  47 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 47 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 47 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 158 (accept_3_2 40 47 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 158
  (Polychromatic418967fa.accept_18_2_11_14_1_69 38 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 158 (accept_3_2 37 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 158 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 47 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 158 (accept_3_2 34 47 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 158
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 158 (accept_3_2 31 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 158 (accept_3_2 28 47 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 158
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 158 (accept_3_2 25 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 47 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 158 (accept_3_2 22 47 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 158
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 158 (accept_3_2 19 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 158 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 158 (accept_3_2 16 47 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 158
  (Polychromatic418967fa.accept_19_14_9_6_1_8633 14 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 158 (accept_3_2 13 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 158 (Polychromatic418967fa.accept_20_11_7_18_1_8632 11 47 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 158 (accept_3_2 10 47 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 158
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 158 (accept_3_2 7 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  158 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 47 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 158 (accept_3_2 4 47 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  47 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 158 (accept_3_2 1 47 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 158))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46
  158 (allA_of_3_0 46 46 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 158 (allA_succ_of_accept 44 45 158
  (Polychromatic418967fa.accept_23_21_22_20_1_8631 44 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 45 158 (accept_3_2 43 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 158 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 45 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 158 (accept_3_2 40 45 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  45 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 158
  (Polychromatic418967fa.accept_13_12_6_2_1_1441 38 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 158 (accept_3_2 37 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 158 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 45 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 158 (accept_3_2 34 45 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 158 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 45 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 158
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 158 (accept_3_2 31 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 158 (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 158 (accept_3_2 28 45 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 158
  (Polychromatic418967fa.accept_16_10_13_14_1_5042 26 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 45 158 (accept_3_2 25 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 45 158 (Polychromatic418967fa.accept_17_7_11_5_1_3539 24 45 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 158 (accept_3_2 22 45 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 158 (Polychromatic418967fa.accept_13_8_6_2_1_865
  21 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 158
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 158 (accept_3_2 19 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 158 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 158 (accept_3_2 16 45 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 158
  (Polychromatic418967fa.accept_13_1_6_2_1_377 14 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 158 (accept_3_2 13 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 158 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 158 (accept_3_2 10 45 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 158 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 45 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 158
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 158 (accept_3_2 7 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  158 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 45 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 158 (accept_3_2 4 45 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 158 (Polychromatic418967fa.accept_10_2_5_8_1_139 2
  45 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 158 (accept_3_2 1 45 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 158))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  158 (allA_succ_of_accept 43 44 158 (accept_3_2 43 44 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  44 158 2 21 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 44 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 44 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 44 158 2 20 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 44 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 44 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 158 2 19 22 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 158 (accept_3_2 37 44 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 158 2 18 22 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 158
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 44 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 44 158 2 17 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 44 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 44 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 44 158 2 16 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 158 (accept_3_2 31 44 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 158 2 15 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 44 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 158 2 14 22 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 158
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 44 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 158 2 13 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 44 158 (accept_3_2 25 44 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44
  158 2 12 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  44 158 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 44 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 44 158 2 11 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 44 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 44 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 158 2 10 22 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 158 (accept_3_2 19 44 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 158 2 9 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 44 158 (Polychromatic418967fa.accept_12_5_8_2_1_309 17
  44 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 158 2 8 22 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 158
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 44 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 44 158 2 7 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 44 158 (accept_3_2 13 44 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44
  158 2 6 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  44 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 44 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 44 158 2 5 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 44 158 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 44 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 158 2 4 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 158 (accept_3_2 7 44 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 158 2 3 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 44 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 44 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 158 2 2 22 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 158
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 44 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 44 158 2 1 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 44 158 (accept_3_2 1 44 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  158)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 158 (allA_of_3_0 43 43 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 42 158 (allA_succ_of_accept 41 42 158 (Polychromatic418967fa.accept_15_11_12_8_1_739 41 42 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 158 2 20 21 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 158
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 42 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 158 2 19 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 158 (accept_3_2 37 42 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42
  158 2 18 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  42 158 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 42 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 42 158 2 17 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 42 158 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 42 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 158 2 16 21 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 158 (accept_3_2 31 42 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 158 2 15 21 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 158
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 42 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 158 2 14 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 42 158 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 42 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 158 2 13 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 158 (accept_3_2 25 42 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 158 2 12 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 158 (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 42 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 158 2 11 21 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 158
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 42 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 158 2 10 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 158 (accept_3_2 19 42 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42
  158 2 9 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  42 158 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 42 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 158 2 8 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 158 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 42 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 158 2 7 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 158 (accept_3_2 13 42 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 158 2 6 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 42 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 42 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 158 2 5 21 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 158
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 42 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 158 2 4 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 158 (accept_3_2 7 42 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 158
  2 3 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42
  158 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 42 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 42 158 2 2 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 42 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 42 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 158 2 1 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 158 (accept_3_2 1 42 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 158)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 158 (allA_succ_of_accept 40 41
  158 (accept_3_2 40 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 41 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 158 (accept_3_2 37 41 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 158 (Polychromatic418967fa.accept_16_4_9_14_1_3883 36 41 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 158 (accept_3_2 34 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 41 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 158 (accept_3_2 31 41 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 41 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 158
  (Polychromatic418967fa.accept_10_9_1_8_1_755 29 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 158 (accept_3_2 28 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 41 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 158 (accept_3_2 25 41 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 41 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 158 (accept_3_2 22 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 41 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 158 (accept_3_2 19 41 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 158 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 41 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 158
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 158 (accept_3_2 16 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 158 (Polychromatic418967fa.accept_21_14_20_11_1_8630 14 41 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 158 (accept_3_2 13 41 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 41 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 158
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 158 (accept_3_2 10 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 158 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 41 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 158 (accept_3_2 7 41 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 158 (Polychromatic418967fa.accept_21_6_20_11_1_7067 6 41 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 158
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 158 (accept_3_2 4 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 41 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 158 (accept_3_2 1 41 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 158))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 158 (allA_of_3_0 40 40 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 158 (allA_succ_of_accept 38 39 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 158 (accept_3_2 37 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 158 (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 158 (accept_3_2 34 39 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 158
  (Polychromatic418967fa.accept_15_2_9_8_1_736 32 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 158 (accept_3_2 31 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 158 (accept_3_2 28 39 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 158 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 39 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 158
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 158 (accept_3_2 25 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 158 (accept_3_2 22 39 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 158 (accept_3_2 19 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 158 (accept_3_2 16 39 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 158 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 39 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 158
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 158 (accept_3_2 13 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 158 (Polychromatic418967fa.accept_18_12_3_14_1_5919 12 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 158 (accept_3_2 10 39 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 158
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 158 (accept_3_2 7 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  158 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 39 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 158 (accept_3_2 4 39 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 158 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 39 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 39
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 158 (accept_3_2 1 39 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 158))))))))))))))))))))))))))))))))))))))) (allB_succ 38 158
  (allA_succ_of_accept 37 38 158 (accept_3_2 37 38 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  158 2 18 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 38 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 158 2 17 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 38 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 158 2 16 19 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 158 (accept_3_2 31 38 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 158 2 15 19 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 158
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 38 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 158 2 14 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 158 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 38 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 158 2 13 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 158 (accept_3_2 25 38 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 158 2 12 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 158 (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 38
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 158 2 11 19 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 158
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 38 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 158 2 10 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 158 (accept_3_2 19 38 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  158 2 9 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 38 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 158 2 8 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 158 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 38 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 158 2 7 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 158 (accept_3_2 13 38 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 158 2 6 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 158 (Polychromatic418967fa.accept_18_11_2_14_1_3351 11 38 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 158 2 5 19 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 158
  (Polychromatic418967fa.accept_22_9_16_4_1_8629 9 38 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 158 2 4 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 158 (accept_3_2 7 38 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 158
  2 3 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  158 (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 38 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 38 158 2 2 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 38 158 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 38 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 158 2 1 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 158 (accept_3_2 1 38 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 38 158)))))))))))))))))))))))))))))))))))))) (allB_succ 37 158 (allA_of_3_0 37 37 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 158 (allA_succ_of_accept 35 36 158
  (Polychromatic418967fa.accept_20_15_16_18_1_5597 35 36 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 36 158 2 17 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 36 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 36 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 158 2 16 18 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 158 (accept_3_2 31 36 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 158 2 15 18 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 158
  (Polychromatic418967fa.accept_11_7_3_4_1_729 29 36 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 36 158 2 14 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 36 158 (Polychromatic418967fa.accept_19_8_17_6_1_5728 27 36 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 158 2 13 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 158 (accept_3_2 25 36 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 158 2 12 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 158 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 36 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 158 2 11 18 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 158
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 21 36 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 36 158 2 10 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 36 158 (accept_3_2 19 36 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36
  158 2 9 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  36 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 36 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 36 158 2 8 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 36 158 (Polychromatic418967fa.accept_16_15_4_14_1_6123 15 36 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 158 2 7 18 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 158 (accept_3_2 13 36 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 158 2 6 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 158 (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 36
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 158 2 5 18 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 158
  (Polychromatic418967fa.accept_16_9_4_14_1_1878 9 36 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 36 158 2 4 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 158 (accept_3_2 7 36 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 158
  2 3 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36
  158 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 36 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 36 158 2 2 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 36 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 36 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 158 2 1 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 158 (accept_3_2 1 36 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 158)))))))))))))))))))))))))))))))))))) (allB_succ 35 158 (allA_succ_of_accept 34 35 158
  (accept_3_2 34 35 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 35 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 158 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 35 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 158 (accept_3_2 31 35 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 35 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 29
  35 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 158 (accept_3_2 28 35
  158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 158 (Polychromatic418967fa.accept_6_3_5_2_1_12
  27 35 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 158
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 35 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 158 (accept_3_2 25 35 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 158 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 158 (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 35 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 158 (accept_3_2 22 35 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 35 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 158
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 35 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 158 (accept_3_2 19 35 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 158 (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 35 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 158 (accept_3_2 16 35 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 158
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 14 35 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 158 (accept_3_2 13 35 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 35 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 158 (accept_3_2 10 35 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 158
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 35 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 158 (accept_3_2 7 35 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  158 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 35 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 158 (accept_3_2 4 35 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  35 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 158 (accept_3_2 1 35 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 158))))))))))))))))))))))))))))))))))) (allB_succ 34 158
  (allA_of_3_0 34 34 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 158 (allA_succ_of_accept 32 33 158
  (Polychromatic418967fa.accept_22_10_11_4_1_6974 32 33 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 158 (accept_3_2 31 33 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 33 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 158 (accept_3_2 28 33 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 158
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 33 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 158 (accept_3_2 25 33 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 158 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 33 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 158 (accept_3_2 22 33 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 33 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 158
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 33 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 158 (accept_3_2 19 33 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 158 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 33 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 158 (accept_3_2 16 33 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 158
  (Polychromatic418967fa.accept_21_14_12_11_1_3956 14 33 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 33 158 (accept_3_2 13 33 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 33 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 33 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 158 (accept_3_2 10 33 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 9
  33 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 158
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 33 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 158 (accept_3_2 7 33 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  158 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 33 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 158 (accept_3_2 4 33 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  33 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 158 (accept_3_2 1 33 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 158))))))))))))))))))))))))))))))))) (allB_succ 32 158
  (allA_succ_of_accept 31 32 158 (accept_3_2 31 32 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32
  158 2 15 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  32 158 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 32 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 158 2 14 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 32 158 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 32 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 158 2 13 16 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 158 (accept_3_2 25 32 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 158 2 12 16 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 158
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 32 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 32 158 2 11 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 32 158 (Polychromatic418967fa.accept_13_8_6_2_1_865 21 32 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 32 158 2 10 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 32 158 (accept_3_2 19 32 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 158 2 9 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 32 158 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 32 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 32 158 2 8 16 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 32 158
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 32 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 32 158 2 7 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 32 158 (accept_3_2 13 32 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32
  158 2 6 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  32 158 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 32 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 32 158 2 5 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 32 158 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 32 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 158 2 4 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 158 (accept_3_2 7 32 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 158 2 3 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 32 158 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 32 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 32 158 2 2 16 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 32 158
  (Polychromatic418967fa.accept_25_3_7_8_1_6701 3 32 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 32 158 2 1 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 32 158 (accept_3_2 1 32 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32
  158)))))))))))))))))))))))))))))))) (allB_succ 31 158 (allA_of_3_0 31 31 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 30 158 (allA_succ_of_accept 29 30 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 30 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 158 2 14 15 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 30 158
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 30 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 30 158 2 13 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 30 158 (accept_3_2 25 30 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30
  158 2 12 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  30 158 (Polychromatic418967fa.accept_11_1_8_4_1_717 23 30 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 30 158 2 11 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 30 158 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 30 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 158 2 10 15 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 158 (accept_3_2 19 30 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 158 2 9 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 158 (Polychromatic418967fa.accept_9_8_3_5_1_241 17
  30 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 158 2 8 15 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 158
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 30 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 30 158 2 7 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 30 158 (accept_3_2 13 30 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30
  158 2 6 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  30 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 30 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 30 158 2 5 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 30 158 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 30 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 158 2 4 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 158 (accept_3_2 7 30 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 158 2 3 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 30 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 30 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 158 2 2 15 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 158
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 30 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 30 158 2 1 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 158 (accept_3_2 1 30 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30
  158)))))))))))))))))))))))))))))) (allB_succ 29 158 (allA_succ_of_accept 28 29 158 (accept_3_2 28 29 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 158
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 29 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 158 (accept_3_2 25 29 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 29 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 29 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 158 (accept_3_2 22 29 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 158
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 29 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 158 (accept_3_2 19 29 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 158 (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 29 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 29 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 158 (accept_3_2 16 29 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 158
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 29 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 158 (accept_3_2 13 29 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 29 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 158 (accept_3_2 10 29 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 158
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 158 (accept_3_2 7 29 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  158 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 29 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 29 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 158 (accept_3_2 4 29 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 158 (Polychromatic418967fa.accept_18_2_11_14_1_69 2
  29 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 158 (accept_3_2 1 29 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 158))))))))))))))))))))))))))))) (allB_succ 28 158 (allA_of_3_0
  28 28 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 158 (allA_succ_of_accept 26 27 158
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 27 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 158 (accept_3_2 25 27 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 27 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 158 (accept_3_2 22 27 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 158
  (Polychromatic418967fa.accept_15_5_12_8_1_3168 20 27 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 158 (accept_3_2 19 27 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 158 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 27 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 158 (accept_3_2 16 27 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 158 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 27 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 158
  (Polychromatic418967fa.accept_17_14_10_5_1_8628 14 27 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 158 (accept_3_2 13 27 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 27 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 158 (accept_3_2 10 27 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 158
  (Polychromatic418967fa.accept_29_8_27_13_1_8627 8 27 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 158 (accept_3_2 7 27 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  158 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 27 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 158 (accept_3_2 4 27 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 27 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 27
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 158 (accept_3_2 1 27 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 158))))))))))))))))))))))))))) (allB_succ 26 158
  (allA_succ_of_accept 25 26 158 (accept_3_2 25 26 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  158 2 12 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 26 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 158 2 11 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 26 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 158 2 10 13 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 158 (accept_3_2 19 26 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 158 2 9 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 158 (Polychromatic418967fa.accept_21_17_5_11_1_7028
  17 26 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 158 2 8 13 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 158
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 26 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 158 2 7 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 158 (accept_3_2 13 26 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  158 2 6 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 26 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 158 2 5 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 26 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 158 2 4 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 158 (accept_3_2 7 26 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 158 2 3 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 158 (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 26 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 158 2 2 13 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 158
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 26 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 158 2 1 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 158 (accept_3_2 1 26 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  158)))))))))))))))))))))))))) (allB_succ 25 158 (allA_of_3_0 25 25 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 158 (allA_succ_of_accept 23 24 158 (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 24 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 158 2 11 12 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 158
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 24 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 158 2 10 12 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 158 (accept_3_2 19 24 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  158 2 9 12 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 158 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 158 2 8 12 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 158 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 24 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 158 2 7 12 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 158 (accept_3_2 13 24 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 158 2 6 12 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 24 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 24 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 158 2 5 12 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 158
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 24 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 158 2 4 12 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 158 (accept_3_2 7 24 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 158
  2 3 12 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  158 (Polychromatic418967fa.accept_22_5_2_4_1_8626 5 24 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 24 158 2 2 12 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 24 158 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 158 2 1 12 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 158 (accept_3_2 1 24 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 24 158)))))))))))))))))))))))) (allB_succ 23 158 (allA_succ_of_accept 22 23 158
  (accept_3_2 22 23 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 23 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 158 (accept_3_2 19 23 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 158 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 23 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  23 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 158 (accept_3_2 16 23
  158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 158 (Polychromatic418967fa.accept_6_3_5_2_1_12
  15 23 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 158
  (Polychromatic418967fa.accept_21_14_2_11_1_8625 14 23 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 158 (accept_3_2 13 23 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 158 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 23 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 158 (Polychromatic418967fa.accept_10_1_3_8_1_136 11 23 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 158 (accept_3_2 10 23 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 158
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 23 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 158 (accept_3_2 7 23 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  158 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 23 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 158 (accept_3_2 4 23 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 158 (Polychromatic418967fa.accept_14_2_9_4_1_1735 2
  23 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 158 (accept_3_2 1 23 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 158))))))))))))))))))))))) (allB_succ 22 158 (allA_of_3_0 22 22
  158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 158 (allA_succ_of_accept 20 21 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 21 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 158 (accept_3_2 19 21 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 158 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 21 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 158 (accept_3_2 16 21 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 158
  (Polychromatic418967fa.accept_15_14_6_8_1_1410 14 21 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 158 (accept_3_2 13 21 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 158 (Polychromatic418967fa.accept_18_12_3_14_1_5919 12 21 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 158 (accept_3_2 10 21 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 158 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 21 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 158
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 21 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 158 (accept_3_2 7 21 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  158 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 21 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 158 (accept_3_2 4 21 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 21
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 158 (accept_3_2 1 21 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 158))))))))))))))))))))) (allB_succ 20 158 (allA_succ_of_accept
  19 20 158 (accept_3_2 19 20 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 158 2 9 10 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 158
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 20 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 158 2 8 10 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 20 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 158 2 7 10 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 158 (accept_3_2 13 20 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 158 2 6 10 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 158 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 20 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 158 2 5 10 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 158 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 20
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 158 2 4 10 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 158 (accept_3_2 7 20
  158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 158 2 3 10 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20 158
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 20 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 158 2 2 10 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 158 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 20 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 158 2 1 10 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 158 (accept_3_2 1 20 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 158)))))))))))))))))))) (allB_succ 19 158 (allA_of_3_0 19 19 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 158 (allA_succ_of_accept 17 18 158 (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 18 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 158 2 8 9 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 158
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 18 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 158 2 7 9 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 158 (accept_3_2 13 18 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  158 2 6 9 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 158 (Polychromatic418967fa.accept_15_11_3_8_1_750 11 18 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 158 2 5 9 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 158 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 18 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 158 2 4 9 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 158 (accept_3_2 7 18 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 158 2 3 9 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 158 (Polychromatic418967fa.accept_15_5_3_8_1_748 5 18 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 158 2 2 9 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 158
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 18 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 158 2 1 9 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 158 (accept_3_2 1 18 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  158)))))))))))))))))) (allB_succ 17 158 (allA_succ_of_accept 16 17 158 (accept_3_2 16 17 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 158
  (Polychromatic418967fa.accept_23_14_17_20_1_8624 14 17 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 17 158 (accept_3_2 13 17 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 17 158 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 17 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 158 (accept_3_2 10 17 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 158
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 17 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 158 (accept_3_2 7 17 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  158 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 17 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 158 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 17 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 158 (accept_3_2 4 17 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 158 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  17 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 158 (accept_3_2 1 17 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 158))))))))))))))))) (allB_succ 16 158 (allA_of_3_0 16 16 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 158 (allA_succ_of_accept 14 15 158
  (Polychromatic418967fa.accept_22_14_15_4_1_8623 14 15 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 158 (accept_3_2 13 15 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 15 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 158 (accept_3_2 10 15 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 158
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 15 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 158 (accept_3_2 7 15 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  158 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 15 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 158 (accept_3_2 4 15 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 15 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 158 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  15 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 158 (accept_3_2 1 15 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 158))))))))))))))) (allB_succ 14 158 (allA_succ_of_accept 13 14
  158 (accept_3_2 13 14 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 158 2 6 7 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 158
  (Polychromatic418967fa.accept_19_11_14_6_1_4378 11 14 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 158 2 5 7 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 158 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 14 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 158 2 4 7 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 158 (accept_3_2 7 14 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 158 2 3 7 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 158 (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 14 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 158 2 2 7 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 158 (Polychromatic418967fa.accept_13_3_1_2_1_2960 3
  14 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 158 2 1 7 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 158 (accept_3_2 1 14
  158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 158)))))))))))))) (allB_succ 13 158 (allA_of_3_0 13 13 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 158 (allA_succ_of_accept 11 12 158
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 12 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 158 2 5 6 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 12 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 158 2 4 6 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 158 (accept_3_2 7 12 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 158 2 3 6 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 158 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 12 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 158 2 2 6 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 158 (Polychromatic418967fa.accept_13_3_12_2_1_385 3
  12 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 158 2 1 6 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 158 (accept_3_2 1 12
  158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 158)))))))))))) (allB_succ 11 158 (allA_succ_of_accept 10 11
  158 (accept_3_2 10 11 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 158
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 158 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 11 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 158 (accept_3_2 7 11 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 158 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 11 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 158 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 158 (accept_3_2 4 11 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 158 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 158
  (Polychromatic418967fa.accept_18_2_11_14_1_69 2 11 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 158 (accept_3_2 1 11 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  158))))))))))) (allB_succ 10 158 (allA_of_3_0 10 10 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 158
  (allA_succ_of_accept 8 9 158 (Polychromatic418967fa.accept_22_8_9_4_1_8622 8 9 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 158 (accept_3_2 7 9 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 158 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 9 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 158 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 158 (accept_3_2 4 9 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9
  158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 158
  (Polychromatic418967fa.accept_11_2_9_4_1_310 2 9 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 158 (accept_3_2 1 9 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 158)))))))))
  (allB_succ 8 158 (allA_succ_of_accept 7 8 158 (accept_3_2 7 8 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 158 2 3 4 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 158 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 8 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 158 2 2 4 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 158 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 8 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 158 2 1 4 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 158 (accept_3_2 1 8 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 158)))))))) (allB_succ 7 158 (allA_of_3_0 7 7 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 158 (allA_succ_of_accept 5 6 158 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 6 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 158 2 2 3 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 158
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 6 158 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 158 2 1 3 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 158 (accept_3_2 1 6 158 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 158))))))
  (allB_succ 5 158 (allA_succ_of_accept 4 5 158 (accept_3_2 4 5 158 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 158 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 5 158 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 158 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 5 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 158 (accept_3_2 1 5 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 158))))) (allB_succ 4 158 (allA_of_3_0 4 4 158 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 158 (allA_succ_of_accept 2 3 158 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 3 158
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 158 (accept_3_2 1 3 158 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 158))) (allB_succ 2 158 (allA_succ_of_accept 1 2 158 (accept_3_2 1 2 158
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 158)) (allB_two
  158))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


