-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch167
-- name    : Polychromatic418967fa_Branch167
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:18:42.321218+00:00
-- url     : https://prove2.me/theorems/d3785cd0-38db-459b-92d3-a3ae2d6f4dc6
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

def Polychromatic418967fa.branch_167 : allB 167 167 :=
  allB_succ' 2 166 167 (Eq.refl Bool.true) (allA_of_3_0 2 166 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  165 167 (Eq.refl Bool.true) (allA_succ_of_accept 2 165 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 165 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 167 (accept_3_2 1 165 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165 167))) (allB_succ' 4 164 167 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 164 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 164 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 164 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 164 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 164 167 (accept_3_2 1 164 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164 167)))) (allB_succ' 5 163 167 (Eq.refl Bool.true) (allA_of_3_0
  5 163 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 162 167 (Eq.refl Bool.true) (allA_succ_of_accept 5
  162 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 162 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 162 167 (accept_3_2 4 162 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 162 167 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 162 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 162 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 162 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 167 (accept_3_2 1 162 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 167)))))) (allB_succ' 7 161 167 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 161 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 161 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 167 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 161
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 167 (accept_3_2 4 161 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 3
  161 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 161 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 167 (accept_3_2 1 161 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161 167)))))))
  (allB_succ' 8 160 167 (Eq.refl Bool.true) (allA_of_3_0 8 160 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 159 167 (Eq.refl Bool.true) (allA_succ_of_accept 8 159 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 159 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 167 (accept_3_2 7 159 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 167 (Polychromatic418967fa.accept_14_6_5_13_1_367
  6 159 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 167
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 5 159 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 167 (accept_3_2 4 159 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 159 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 159 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 167 (accept_3_2 1 159 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159 167))))))))) (allB_succ' 10 158 167 (Eq.refl Bool.true) (allA_succ_of_accept 9 158
  167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 158 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 158 167 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 158 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 158 167 (accept_3_2 7 158 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 158 167 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 158 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 158 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  158 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 158 167 (accept_3_2 4 158
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 158 167 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 158 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 158 167
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 158 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 158 167 (accept_3_2 1 158 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  167)))))))))) (allB_succ' 11 157 167 (Eq.refl Bool.true) (allA_of_3_0 11 157 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 156 167 (Eq.refl Bool.true) (allA_succ_of_accept 11 156 167
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 156 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 156 167 (accept_3_2 10 156 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  156 167 (Polychromatic418967fa.accept_18_9_12_5_1_864 9 156 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 156 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 156 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 167 (accept_3_2 7 156 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 156 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 156 167
  (Polychromatic418967fa.accept_16_5_12_7_1_3411 5 156 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 156 167 (accept_3_2 4 156 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  156 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 156 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 156 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 156 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 167 (accept_3_2 1 156 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 156 167)))))))))))) (allB_succ' 13 155 167 (Eq.refl Bool.true) (allA_succ_of_accept 12
  155 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 155 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 167 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 155 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 167 (accept_3_2 10 155 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 155 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 155 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 167 (accept_3_2 7 155 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 155 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 155 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 167 (accept_3_2 4 155 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 155 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 167
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 155 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 167 (accept_3_2 1 155 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  167))))))))))))) (allB_succ' 14 154 167 (Eq.refl Bool.true) (allA_of_3_0 14 154 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 153 167 (Eq.refl Bool.true) (allA_succ_of_accept 14 153 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 153 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 153 167 (accept_3_2 13 153 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 153 167 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 153 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 153 167 (Polychromatic418967fa.accept_19_11_1_15_1_9263 11 153 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 167 (accept_3_2 10 153 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 167 (Polychromatic418967fa.accept_21_9_6_20_1_1903 9 153
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 153 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 167 (accept_3_2 7 153 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  153 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 153 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 153 167 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 153 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 167 (accept_3_2 4 153 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 153 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 153 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 167 (accept_3_2 1 153 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  167))))))))))))))) (allB_succ' 16 152 167 (Eq.refl Bool.true) (allA_succ_of_accept 15 152 167
  (Polychromatic418967fa.accept_6_3_2_5_1_32 15 152 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 152 167 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 152 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 152 167 (accept_3_2 13 152 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 152 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 152 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 152 167 (Polychromatic418967fa.accept_7_4_5_6_1_344
  11 152 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 152 167 (accept_3_2 10
  152 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 152 167
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 152 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 152 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 152 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 152 167 (accept_3_2 7 152 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 152 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 152 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 152 167 (Polychromatic418967fa.accept_10_5_2_7_1_345 5
  152 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 167 (accept_3_2 4 152
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 152 167 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 152 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 152 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 152 167 (accept_3_2 1 152 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  167)))))))))))))))) (allB_succ' 17 151 167 (Eq.refl Bool.true) (allA_of_3_0 17 151 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 150 167 (Eq.refl Bool.true) (allA_succ_of_accept 17 150 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 150 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 150 167 (accept_3_2 16 150 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 150 167 (Polychromatic418967fa.accept_16_15_6_7_1_4512 15 150 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 150 167 (Polychromatic418967fa.accept_13_1_7_11_1_702 14 150 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 167 (accept_3_2 13 150 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 150 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 150 167
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 150 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 150 167 (accept_3_2 10 150 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  150 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 150 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 150 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 150 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 167 (accept_3_2 7 150 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 167 (Polychromatic418967fa.accept_21_6_3_20_1_6053 6 150 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 150 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 150 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 150 167 (accept_3_2 4 150 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  150 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 150 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 150 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 150 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 167 (accept_3_2 1 150 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 150 167)))))))))))))))))) (allB_succ' 19 149 167 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 149 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 149 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 149 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 167 (accept_3_2 16 149 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  149 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 149 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 167 (accept_3_2 13 149 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 167 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 149 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 149 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 167 (accept_3_2 10 149 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 167 (Polychromatic418967fa.accept_21_9_2_20_1_857 9 149 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 167
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 149 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 167 (accept_3_2 7 149 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 149 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 167 (Polychromatic418967fa.accept_13_5_6_11_1_1933 5 149 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 167 (accept_3_2 4 149 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 149 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 149 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 167 (accept_3_2 1 149 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  167))))))))))))))))))) (allB_succ' 20 148 167 (Eq.refl Bool.true) (allA_of_3_0 20 148 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 147 167 (Eq.refl Bool.true) (allA_succ_of_accept 20 147 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 147 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 147 167 (accept_3_2 19 147 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 147 167 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 147 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 147 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 147 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 167 (accept_3_2 16 147 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 147 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 147 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 147 167 (accept_3_2 13 147 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 147 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 147 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 147 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 147 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 167 (accept_3_2 10 147 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 167 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 147 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 147 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 147 167 (accept_3_2 7 147 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  147 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 147 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 147 167 (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 147 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 167 (accept_3_2 4 147 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 167 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 147 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 147 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 147 167 (accept_3_2 1 147 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  167))))))))))))))))))))) (allB_succ' 22 146 167 (Eq.refl Bool.true) (allA_succ_of_accept 21 146 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 146 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 146 167 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 146 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 146 167 (accept_3_2 19 146 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 146 167 (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 146 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 146 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 146 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 146 167 (accept_3_2 16 146 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 146 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 146 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 146 167 (Polychromatic418967fa.accept_13_1_3_11_1_1289 14 146 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 146 167 (accept_3_2 13 146 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 146 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 146 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 146 167
  (Polychromatic418967fa.accept_10_1_6_7_1_710 11 146 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 146 167 (accept_3_2 10 146 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  146 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 146 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 146 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 146 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 146 167 (accept_3_2 7 146 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 146 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 146 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 146 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 146 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 146 167 (accept_3_2 4 146 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  146 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 146 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 146 167 (Polychromatic418967fa.accept_13_2_3_11_1_1287 2 146 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 146 167 (accept_3_2 1 146 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 146 167)))))))))))))))))))))) (allB_succ' 23 145 167 (Eq.refl Bool.true)
  (allA_of_3_0 23 145 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 144 167 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 144 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 144 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 167 (accept_3_2 22 144 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 144 167 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 144 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 167
  (Polychromatic418967fa.accept_13_7_1_11_1_732 20 144 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 144 167 (accept_3_2 19 144 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 144 167 (Polychromatic418967fa.accept_27_18_9_5_1_9293 18 144 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 144 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 144 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 167 (accept_3_2 16 144 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 167 (Polychromatic418967fa.accept_21_15_18_20_1_9292 15 144 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 144 167
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 144 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 144 167 (accept_3_2 13 144 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 144 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 144 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 144 167 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 144 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 167 (accept_3_2 10 144 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 144 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 144 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 144 167
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 8 144 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 144 167 (accept_3_2 7 144 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  144 167 (Polychromatic418967fa.accept_17_6_8_14_1_6706 6 144 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 144 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 144 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 167 (accept_3_2 4 144 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 144 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 144 167
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 144 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 144 167 (accept_3_2 1 144 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  167)))))))))))))))))))))))) (allB_succ' 25 143 167 (Eq.refl Bool.true) (allA_succ_of_accept 24 143 167
  (Polychromatic418967fa.accept_9_6_8_5_1_837 24 143 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 143 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 143 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 167 (accept_3_2 22 143 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 143 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 143 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 167 (Polychromatic418967fa.accept_9_2_8_5_1_228
  20 143 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 167 (accept_3_2 19
  143 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 167
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 143 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 143 167 (Polychromatic418967fa.accept_19_17_10_15_1_7927 17 143 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 167 (accept_3_2 16 143 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 143 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 167
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 143 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 167 (accept_3_2 13 143 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 143 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 143 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 167 (accept_3_2 10 143 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 143 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 167
  (Polychromatic418967fa.accept_16_8_15_7_1_5658 8 143 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 167 (accept_3_2 7 143 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 143 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 167 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 143 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 167 (accept_3_2 4 143 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 143 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 167
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 143 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 167 (accept_3_2 1 143 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  167))))))))))))))))))))))))) (allB_succ' 26 142 167 (Eq.refl Bool.true) (allA_of_3_0 26 142 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 141 167 (Eq.refl Bool.true) (allA_succ_of_accept 26 141 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 141 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 141 167 (accept_3_2 25 141 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 141 167 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 141 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 141 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 141 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 167 (accept_3_2 22 141 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 141 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 141 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 167 (accept_3_2 19 141 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 141 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 141 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 141 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 141 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 167 (accept_3_2 16 141 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 167 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 141 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 141 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 167 (accept_3_2 13 141 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 141 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 141 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 141 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 141 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 167 (accept_3_2 10 141 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 141 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 141 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 167 (accept_3_2 7 141 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  141 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 141 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 141 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 141 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 167 (accept_3_2 4 141 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 141 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 167 (accept_3_2 1 141 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  167))))))))))))))))))))))))))) (allB_succ' 28 140 167 (Eq.refl Bool.true) (allA_succ_of_accept 27 140 167
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 140 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 140 167 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 140 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 140 167 (accept_3_2 25 140 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 140 167 (Polychromatic418967fa.accept_16_8_12_7_1_2399 24 140 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 140 167
  (Polychromatic418967fa.accept_21_2_14_20_1_841 23 140 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 140 167 (accept_3_2 22 140 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 140 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 140 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 140 167 (Polychromatic418967fa.accept_16_4_12_7_1_4475 20 140 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 140 167 (accept_3_2 19 140 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 140 167 (Polychromatic418967fa.accept_15_3_5_2_1_2816 18 140
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 140 167
  (Polychromatic418967fa.accept_13_4_10_11_1_1908 17 140 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 140 167 (accept_3_2 16 140 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 140 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 140 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 140 167 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 140
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 140 167 (accept_3_2 13 140
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 140 167
  (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 140 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 140 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 140 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 140 167 (accept_3_2 10 140 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 140 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 140 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 140 167
  (Polychromatic418967fa.accept_13_8_10_11_1_2730 8 140 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 140 167 (accept_3_2 7 140 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  140 167 (Polychromatic418967fa.accept_21_6_14_20_1_4594 6 140 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 140 167 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 140 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 140 167 (accept_3_2 4 140 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 167
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 140 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 167 (accept_3_2 1 140 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  167)))))))))))))))))))))))))))) (allB_succ' 29 139 167 (Eq.refl Bool.true) (allA_of_3_0 29 139 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 138 167 (Eq.refl Bool.true) (allA_succ_of_accept 29 138 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 138 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 138 167 (accept_3_2 28 138 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 138 167 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 138 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 138 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 138 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 167 (accept_3_2 25 138 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 138 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 138 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 138 167
  (Polychromatic418967fa.accept_13_10_8_11_1_1985 23 138 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 138 167 (accept_3_2 22 138 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 138 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 138 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 138 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 167 (accept_3_2 19 138 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 138 167 (Polychromatic418967fa.accept_7_4_5_6_1_344
  18 138 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 138 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 138 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 138 167 (accept_3_2 16 138 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 138 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 138 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 138 167 (Polychromatic418967fa.accept_13_1_8_11_1_724 14 138 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 167 (accept_3_2 13 138 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 138 167 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 138
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 138 167
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 138 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 138 167 (accept_3_2 10 138 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  138 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 138 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 138 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 138 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 167 (accept_3_2 7 138 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 138 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 138 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 138 167 (accept_3_2 4 138 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  138 167 (Polychromatic418967fa.accept_13_3_8_11_1_1906 3 138 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 138 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 138 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 167 (accept_3_2 1 138 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 138 167)))))))))))))))))))))))))))))) (allB_succ' 31 137 167 (Eq.refl Bool.true)
  (allA_succ_of_accept 30 137 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 137 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 167 (Polychromatic418967fa.accept_13_3_7_11_1_1904 29 137
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 167 (accept_3_2 28 137
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 167
  (Polychromatic418967fa.accept_13_1_7_11_1_702 27 137 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 137 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 137 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 167 (accept_3_2 25 137 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 137 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 137 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 167 (Polychromatic418967fa.accept_7_2_4_6_1_166
  23 137 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 167 (accept_3_2 22
  137 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 167
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 137 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 137 167 (Polychromatic418967fa.accept_19_1_4_15_1_2542 20 137 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 167 (accept_3_2 19 137 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 137 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 137 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 167 (Polychromatic418967fa.accept_7_3_4_6_1_329
  17 137 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 167 (accept_3_2 16
  137 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 167
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 137 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 137 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 137 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 167 (accept_3_2 13 137 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 137 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 137 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 167
  (Polychromatic418967fa.accept_19_11_4_15_1_5052 11 137 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 137 167 (accept_3_2 10 137 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 137 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 137 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 137 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 167 (accept_3_2 7 137 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  137 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 167
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 137 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 167 (accept_3_2 4 137 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 137 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 167 (accept_3_2 1 137 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 137 167))))))))))))))))))))))))))))))) (allB_succ' 32 136 167 (Eq.refl Bool.true)
  (allA_of_3_0 32 136 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 135 167 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 135 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 135 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 167 (accept_3_2 31 135 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 135 167 (Polychromatic418967fa.accept_18_12_9_5_1_2771 30 135 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 167
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 135 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 167 (accept_3_2 28 135 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 135 167 (Polychromatic418967fa.accept_19_8_2_15_1_2426 27 135 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 135 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 135 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 167 (accept_3_2 25 135 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 135 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 167
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 135 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 167 (accept_3_2 22 135 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 135 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 135 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 135 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 135 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 167 (accept_3_2 19 135 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 135 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 167
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 135 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 167 (accept_3_2 16 135 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 135 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 135 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 135 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 135 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 167 (accept_3_2 13 135 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 167 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 135 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 167
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 135 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 167 (accept_3_2 10 135 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  135 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 135 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 167 (accept_3_2 7 135 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 167 (Polychromatic418967fa.accept_13_6_5_11_1_1971 6 135 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 167
  (Polychromatic418967fa.accept_20_5_15_7_1_7869 5 135 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 167 (accept_3_2 4 135 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 135 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 135 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 167 (accept_3_2 1 135 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 135 167))))))))))))))))))))))))))))))))) (allB_succ' 34 134 167 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 134 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 134 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 134 167 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 134
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 134 167 (accept_3_2 31 134
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 134 167
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 134 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 134 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 134 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 134 167 (accept_3_2 28 134 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 134 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 134 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 134 167 (Polychromatic418967fa.accept_7_5_1_6_1_163
  26 134 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 134 167 (accept_3_2 25
  134 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 134 167
  (Polychromatic418967fa.accept_9_6_8_5_1_837 24 134 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 134 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 134 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 134 167 (accept_3_2 22 134 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 134 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 134 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 134 167 (Polychromatic418967fa.accept_9_2_8_5_1_228
  20 134 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 134 167 (accept_3_2 19
  134 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 134 167
  (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 134 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 134 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 134 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 167 (accept_3_2 16 134 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 134 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 134 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 134 167 (Polychromatic418967fa.accept_18_14_8_5_1_860
  14 134 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 134 167 (accept_3_2 13
  134 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 134 167
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 134 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 134 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 134 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 167 (accept_3_2 10 134 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 134 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 134 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 167 (Polychromatic418967fa.accept_12_8_2_11_1_246
  8 134 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 134 167 (accept_3_2 7
  134 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 134 167
  (Polychromatic418967fa.accept_9_6_8_5_1_837 6 134 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 134 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 134 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 167 (accept_3_2 4 134 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 134 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 134 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  134 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 134 167 (accept_3_2 1 134
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134 167)))))))))))))))))))))))))))))))))) (allB_succ' 35 133
  167 (Eq.refl Bool.true) (allA_of_3_0 35 133 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 132 167
  (Eq.refl Bool.true) (allA_succ_of_accept 35 132 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 132 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 167 (accept_3_2 34 132 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 132 167 (Polychromatic418967fa.accept_14_5_6_13_1_3145 33 132
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 167
  (Polychromatic418967fa.accept_21_11_6_20_1_4589 32 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 132 167 (accept_3_2 31 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 132 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 132 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 132 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 132 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 167 (accept_3_2 28 132 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 132 167 (Polychromatic418967fa.accept_8_3_4_7_1_475
  27 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 167
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 132 167 (accept_3_2 25 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 132 167 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 132 167 (Polychromatic418967fa.accept_13_10_2_11_1_1920 23 132 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 167 (accept_3_2 22 132 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 132 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 132 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 167
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 132 167 (accept_3_2 19 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 132 167 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 132 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 132 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 167 (accept_3_2 16 132 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 132 167 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 132 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 167
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 132 167 (accept_3_2 13 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 132 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 132 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 132 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 167 (accept_3_2 10 132 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 167 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 132 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 167
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 167 (accept_3_2 7 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  132 167 (Polychromatic418967fa.accept_15_6_12_2_1_2803 6 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 132 167 (Polychromatic418967fa.accept_10_5_2_7_1_345 5 132 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 167 (accept_3_2 4 132 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 132 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 167
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 167 (accept_3_2 1 132 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  167)))))))))))))))))))))))))))))))))))) (allB_succ' 37 131 167 (Eq.refl Bool.true) (allA_succ_of_accept 36 131 167
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 131 167 (Polychromatic418967fa.accept_13_9_1_11_1_275 35 131 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 167 (accept_3_2 34 131 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 131 167 (Polychromatic418967fa.accept_13_7_1_11_1_732 33 131 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 167
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 167 (accept_3_2 31 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 167 (Polychromatic418967fa.accept_20_10_11_7_1_4796 30 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 131 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 167 (accept_3_2 28 131 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 167 (Polychromatic418967fa.accept_16_11_3_7_1_2375 27 131 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 167
  (Polychromatic418967fa.accept_10_6_1_7_1_342 26 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 167 (accept_3_2 25 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 167 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 167 (Polychromatic418967fa.accept_11_1_10_2_1_58 23 131 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 167 (accept_3_2 22 131 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 167 (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 131
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 167
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 167 (accept_3_2 19 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 167 (Polychromatic418967fa.accept_22_17_21_13_1_9291 17 131 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 167 (accept_3_2 16 131 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 131 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 167
  (Polychromatic418967fa.accept_10_4_1_7_1_371 14 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 167 (accept_3_2 13 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 131 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 167 (accept_3_2 10 131 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 167 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 131 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 167
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 167 (accept_3_2 7 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 167 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 167 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 131 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 167 (accept_3_2 4 131 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 167 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 131
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 167
  (Polychromatic418967fa.accept_19_2_17_15_1_1377 2 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 167 (accept_3_2 1 131 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  167))))))))))))))))))))))))))))))))))))) (allB_succ' 38 130 167 (Eq.refl Bool.true) (allA_of_3_0 38 130 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 129 167 (Eq.refl Bool.true) (allA_succ_of_accept 38 129 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 129 167 (accept_3_2 37 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 129 167 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 129 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 129 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 167 (accept_3_2 34 129 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 129 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 167 (accept_3_2 31 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 129 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 129 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 129 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 167 (accept_3_2 28 129 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 167 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 129 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 167 (accept_3_2 25 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 129 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 129 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 129 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 167 (accept_3_2 22 129 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 167 (Polychromatic418967fa.accept_22_21_19_13_1_9290 21 129 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 167 (accept_3_2 19 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 129 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 167 (accept_3_2 16 129 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 129 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 167 (accept_3_2 13 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 167 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 129 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 167 (accept_3_2 10 129 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 129 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 167 (accept_3_2 7 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 167 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 129 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 167 (accept_3_2 4 129 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 129 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 167 (accept_3_2 1 129 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  167))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 128 167 (Eq.refl Bool.true) (allA_succ_of_accept 39 128 167
  (Polychromatic418967fa.accept_6_3_2_5_1_32 39 128 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 128 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 128 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 128 167 (accept_3_2 37 128 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 128 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 128 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 128 167 (Polychromatic418967fa.accept_9_8_2_5_1_237
  35 128 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 128 167 (accept_3_2 34
  128 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 128 167
  (Polychromatic418967fa.accept_6_3_2_5_1_32 33 128 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 128 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 128 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 128 167 (accept_3_2 31 128 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 128 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 128 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 128 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 29
  128 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 128 167 (accept_3_2 28
  128 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 128 167
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 128 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 128 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 128 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 128 167 (accept_3_2 25 128 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 128 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 128 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 128 167
  (Polychromatic418967fa.accept_19_4_14_15_1_9231 23 128 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 128 167 (accept_3_2 22 128 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 128 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 128 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 128 167 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 128
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 128 167 (accept_3_2 19 128
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 128 167
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 128 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 128 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 128 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 128 167 (accept_3_2 16 128 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 128 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 128 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 167 (Polychromatic418967fa.accept_12_2_8_11_1_31
  14 128 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 128 167 (accept_3_2 13
  128 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 128 167
  (Polychromatic418967fa.accept_9_3_2_5_1_234 12 128 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 128 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 128 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 128 167 (accept_3_2 10 128 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 128 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 8
  128 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 128 167 (accept_3_2 7 128
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 128 167
  (Polychromatic418967fa.accept_9_6_2_5_1_506 6 128 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 128 167 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 128 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 167 (accept_3_2 4 128 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 128 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 167 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  128 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 128 167 (accept_3_2 1 128
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128 167)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41
  127 167 (Eq.refl Bool.true) (allA_of_3_0 41 127 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 126 167
  (Eq.refl Bool.true) (allA_succ_of_accept 41 126 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 126 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 167 (accept_3_2 40 126 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 126 167 (Polychromatic418967fa.accept_20_19_6_7_1_9289 39 126
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 126 167
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 38 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 126 167 (accept_3_2 37 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 126 167 (Polychromatic418967fa.accept_16_4_14_7_1_5641 36 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 126 167 (Polychromatic418967fa.accept_19_16_12_15_1_6449 35 126 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 126 167 (accept_3_2 34 126 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 126 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 126 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 126 167
  (Polychromatic418967fa.accept_20_12_6_7_1_7875 32 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 126 167 (accept_3_2 31 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 126 167 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 126 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 126 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 167 (accept_3_2 28 126 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 126 167 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 126 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 126 167
  (Polychromatic418967fa.accept_15_11_6_2_1_1106 26 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 126 167 (accept_3_2 25 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 126 167 (Polychromatic418967fa.accept_19_5_12_15_1_9244 24 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 126 167 (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 126 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 167 (accept_3_2 22 126 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 126 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 126 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 126 167
  (Polychromatic418967fa.accept_13_7_9_11_1_705 20 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 126 167 (accept_3_2 19 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 126 167 (Polychromatic418967fa.accept_19_18_12_15_1_9288 18 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 126 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 126 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 167 (accept_3_2 16 126 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 167 (Polychromatic418967fa.accept_13_2_9_11_1_258 15 126
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 126 167
  (Polychromatic418967fa.accept_13_1_9_11_1_703 14 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 126 167 (accept_3_2 13 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 126 167 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 126 167 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 126 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 167 (accept_3_2 10 126 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 126 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 167
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 126 167 (accept_3_2 7 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  126 167 (Polychromatic418967fa.accept_17_6_7_14_1_6704 6 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 126 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 167 (accept_3_2 4 126 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 167 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 126 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 167
  (Polychromatic418967fa.accept_13_2_9_11_1_258 2 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 126 167 (accept_3_2 1 126 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  167)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 125 167 (Eq.refl Bool.true) (allA_succ_of_accept 42 125
  167 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 125 167 (Polychromatic418967fa.accept_15_11_5_2_1_520 41 125 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 167 (accept_3_2 40 125 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 125 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 125 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  125 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 167 (accept_3_2 37
  125 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 167
  (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 167 (Polychromatic418967fa.accept_13_9_8_11_1_725 35 125 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 167 (accept_3_2 34 125 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 125 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 167
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 167 (accept_3_2 31 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 125 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 167 (accept_3_2 28 125 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 167 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 125 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 167 (accept_3_2 25 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 167 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 125 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 167 (accept_3_2 22 125 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 125 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 167 (accept_3_2 19 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 167 (Polychromatic418967fa.accept_11_6_4_2_1_599 17 125 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 167 (accept_3_2 16 125 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 125 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 167 (accept_3_2 13 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 125 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 167 (accept_3_2 10 125 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 167 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 125 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 167
  (Polychromatic418967fa.accept_10_8_5_7_1_358 8 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 167 (accept_3_2 7 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 167 (Polychromatic418967fa.accept_19_5_11_15_1_2460 5 125 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 167 (accept_3_2 4 125 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 125 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 167 (accept_3_2 1 125 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  167))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 124 167 (Eq.refl Bool.true) (allA_of_3_0 44 124 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 123 167 (Eq.refl Bool.true) (allA_succ_of_accept 44 123 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 123 167 (accept_3_2 43 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 123 167 (Polychromatic418967fa.accept_15_12_3_2_1_2756 42 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 123 167 (Polychromatic418967fa.accept_17_7_4_14_1_2106 41 123 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 167 (accept_3_2 40 123 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 123 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 123 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 123 167 (accept_3_2 37 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 123 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 123 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 123 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 167 (accept_3_2 34 123 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 123 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 123 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 123 167 (accept_3_2 31 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 123 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 123 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 123 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 167 (accept_3_2 28 123 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 123 167 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 123 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 167 (accept_3_2 25 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 123 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 123 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 123 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 167 (accept_3_2 22 123 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 123 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 123 167 (accept_3_2 19 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 123 167 (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 123 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 123 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 167 (accept_3_2 16 123 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 167 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 123 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 123 167 (accept_3_2 13 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 123 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 123 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 123 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 167 (accept_3_2 10 123 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 123 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 167 (accept_3_2 7 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  123 167 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 123 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 123 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 167 (accept_3_2 4 123 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 123 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 167 (accept_3_2 1 123 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  167))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 122 167 (Eq.refl Bool.true) (allA_succ_of_accept 45
  122 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 122 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 122 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 122 167 (accept_3_2 43 122 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 122 167 (Polychromatic418967fa.accept_13_3_5_11_1_716 42 122 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 122 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 122 167 (accept_3_2 40 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 122 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 122 167 (Polychromatic418967fa.accept_20_18_2_7_1_6285 38 122 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 122 167 (accept_3_2 37 122 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 122 167 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 122
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 122 167
  (Polychromatic418967fa.accept_10_5_2_7_1_345 35 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 122 167 (accept_3_2 34 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 122 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 122 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 122 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 122 167 (accept_3_2 31 122 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 122 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 122 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 122 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 122 167 (accept_3_2 28 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 122 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 122 167 (Polychromatic418967fa.accept_18_8_14_5_1_2778 26 122 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 122 167 (accept_3_2 25 122 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 122 167 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 122
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 122 167
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 122 167 (accept_3_2 22 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 122 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 122 167 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 122 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 122 167 (accept_3_2 19 122 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 122 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 122 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 122 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 122 167 (accept_3_2 16 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 122 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 122 167 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 122 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 122 167 (accept_3_2 13 122 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 122 167 (Polychromatic418967fa.accept_19_12_8_15_1_5067 12 122
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 122 167
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 122 167 (accept_3_2 10 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  122 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 122 167 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 122 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 122 167 (accept_3_2 7 122 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 122 167 (Polychromatic418967fa.accept_13_6_5_11_1_1971 6 122 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 122 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 122 167 (accept_3_2 4 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  122 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 122 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 122 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 122 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 122 167 (accept_3_2 1 122 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 122 167)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 121 167 (Eq.refl
  Bool.true) (allA_of_3_0 47 121 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 120 167 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 120 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 120 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 167 (accept_3_2 46 120 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 120 167 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 120 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 120 167
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 120 167 (accept_3_2 43 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 120 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 120 167 (Polychromatic418967fa.accept_13_2_3_11_1_1287 41 120 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 167 (accept_3_2 40 120 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 120 167 (Polychromatic418967fa.accept_21_18_15_20_1_6076 39
  120 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 120 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 120 167 (accept_3_2 37 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 120 167 (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 120 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 120 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 167 (accept_3_2 34 120 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 120 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 167
  (Polychromatic418967fa.accept_19_13_6_15_1_9287 32 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 120 167 (accept_3_2 31 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 120 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 120 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 120 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 120 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 167 (accept_3_2 28 120 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 167
  (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 120 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 120 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 167 (accept_3_2 25 120 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 120 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 120 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 120 167 (Polychromatic418967fa.accept_7_2_1_6_1_173
  23 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 167 (accept_3_2 22
  120 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 167
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 21 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 120 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 120 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 167 (accept_3_2 19 120 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 120 167 (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 120 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 120 167 (accept_3_2 16 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 120 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 120 167 (Polychromatic418967fa.accept_13_1_3_11_1_1289 14 120 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 167 (accept_3_2 13 120 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 120 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 120 167 (accept_3_2 10 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  120 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 120 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 120 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 167 (accept_3_2 7 120 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 120 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 120 167
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 120 167 (accept_3_2 4 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  120 167 (Polychromatic418967fa.accept_22_3_10_13_1_9286 3 120 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 120 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 120 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 167 (accept_3_2 1 120 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 120 167)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 119 167 (Eq.refl
  Bool.true) (allA_succ_of_accept 48 119 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 119 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 167
  (Polychromatic418967fa.accept_19_9_5_15_1_2544 47 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 119 167 (accept_3_2 46 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 119 167 (Polychromatic418967fa.accept_22_1_9_13_1_2894 45 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 119 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 119 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 167 (accept_3_2 43 119 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 119 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 119 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 167
  (Polychromatic418967fa.accept_25_16_19_17_1_9285 41 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 119 167 (accept_3_2 40 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 119 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 119 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 167 (Polychromatic418967fa.accept_10_8_9_7_1_1118 38 119
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 167 (accept_3_2 37 119
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 167
  (Polychromatic418967fa.accept_13_10_2_11_1_1920 36 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 119 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 167 (accept_3_2 34 119 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 119 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 167
  (Polychromatic418967fa.accept_10_2_9_7_1_720 32 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 167 (accept_3_2 31 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 167 (Polychromatic418967fa.accept_11_7_9_2_1_260 29 119 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 167 (accept_3_2 28 119 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 167 (Polychromatic418967fa.accept_15_12_14_2_1_3794 27 119
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 167 (accept_3_2 25 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 167 (Polychromatic418967fa.accept_13_10_2_11_1_1920 23 119 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 167 (accept_3_2 22 119 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 119 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 167
  (Polychromatic418967fa.accept_14_6_7_13_1_3158 20 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 167 (accept_3_2 19 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 167 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 119 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 167 (accept_3_2 16 119 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 119 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 167
  (Polychromatic418967fa.accept_18_14_11_5_1_7967 14 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 119 167 (accept_3_2 13 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 119 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 119 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 167 (Polychromatic418967fa.accept_19_11_5_15_1_2436 11 119
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 167 (accept_3_2 10 119
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 167
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 119 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 119 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 167 (accept_3_2 7 119 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 119 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 119 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 167 (Polychromatic418967fa.accept_15_5_14_2_1_1876
  5 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 167 (accept_3_2 4
  119 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 167
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 119 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 119 167 (Polychromatic418967fa.accept_10_2_9_7_1_720 2 119 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 167 (accept_3_2 1 119 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 119 167))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 118 167 (Eq.refl
  Bool.true) (allA_of_3_0 50 118 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 117 167 (Eq.refl Bool.true)
  (allA_succ_of_accept 50 117 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 117 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 167 (accept_3_2 49 117 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 117 167 (Polychromatic418967fa.accept_14_6_5_13_1_367 48 117 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 167
  (Polychromatic418967fa.accept_19_9_3_15_1_2429 47 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 167 (accept_3_2 46 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 167 (Polychromatic418967fa.accept_19_7_3_15_1_2428 45 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 117 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 167 (accept_3_2 43 117 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 117 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 167
  (Polychromatic418967fa.accept_22_19_7_13_1_6004 41 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 117 167 (accept_3_2 40 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 117 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 117 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 117 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 167 (accept_3_2 37 117 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 36
  117 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 167
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 35 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 167 (accept_3_2 34 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 167 (Polychromatic418967fa.accept_15_3_12_2_1_507 33 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 167 (accept_3_2 31 117 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 117 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 167
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 167 (accept_3_2 28 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 117 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 117 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 117 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 167 (accept_3_2 25 117 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 167 (Polychromatic418967fa.accept_20_4_17_7_1_3393 24 117 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 167
  (Polychromatic418967fa.accept_17_6_15_14_1_8027 23 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 117 167 (accept_3_2 22 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 117 167 (Polychromatic418967fa.accept_15_6_12_2_1_2803 21 117 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 167 (accept_3_2 19 117 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  117 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 167
  (Polychromatic418967fa.accept_19_17_3_15_1_9284 17 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 117 167 (accept_3_2 16 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 117 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 117 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 117 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 167 (accept_3_2 13 117 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 167
  (Polychromatic418967fa.accept_16_12_5_7_1_2360 12 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 117 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 117 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 167 (accept_3_2 10 117 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 117 167 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 117 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 8
  117 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 167 (accept_3_2 7 117
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 167 (Polychromatic418967fa.accept_4_2_1_3_1_27
  6 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 167
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 167 (accept_3_2 4 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 117 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 167 (accept_3_2 1 117 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 117 167))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 116 167
  (Eq.refl Bool.true) (allA_succ_of_accept 51 116 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 116 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 116 167
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 116 167 (accept_3_2 49 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 116 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 116 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 116 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 116 167 (accept_3_2 46 116 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 116 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 116 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 116 167
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 116 167 (accept_3_2 43 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 116 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 116 167 (Polychromatic418967fa.accept_10_1_6_7_1_710 41 116 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 116 167 (accept_3_2 40 116 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 116 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 116 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 116 167
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 116 167 (accept_3_2 37 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 116 167 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 116 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 116 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 116 167 (accept_3_2 34 116 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 116 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 116 167
  (Polychromatic418967fa.accept_18_14_8_5_1_860 32 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 116 167 (accept_3_2 31 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 116 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 116 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 116 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 116 167 (accept_3_2 28 116 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 116 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 116 167
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 116 167 (accept_3_2 25 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 116 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 116 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 116 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 116 167 (accept_3_2 22 116 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 116 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 116 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 116 167 (accept_3_2 19 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 116 167 (Polychromatic418967fa.accept_19_18_2_15_1_3718 18 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 116 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 116 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 116 167 (accept_3_2 16 116 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 116 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 116 167
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 116 167 (accept_3_2 13 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 116 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 116 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 116 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 116 167 (accept_3_2 10 116 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 116 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 116 167
  (Polychromatic418967fa.accept_16_8_4_7_1_3390 8 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 116 167 (accept_3_2 7 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  116 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 116 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 116 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 167 (accept_3_2 4 116 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 116 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 167
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 116 167 (accept_3_2 1 116 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  167)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 115 167 (Eq.refl Bool.true) (allA_of_3_0 53 115
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 114 167 (Eq.refl Bool.true) (allA_succ_of_accept 53 114
  167 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 114 167 (accept_3_2 52 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 114 167 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 114 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 114 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 167 (accept_3_2 49 114 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 114 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 114 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 114 167
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 114 167 (accept_3_2 46 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 114 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 114 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 114 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 167 (accept_3_2 43 114 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 114 167 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 114 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 114 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 114 167 (accept_3_2 40 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 114 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 114 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 114 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 167 (accept_3_2 37 114 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 114 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 114 167
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 114 167 (accept_3_2 34 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 114 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 114 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 114 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 167 (accept_3_2 31 114 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 114 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 114 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 114 167 (accept_3_2 28 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 114 167 (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 114 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 114 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 167 (accept_3_2 25 114 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 114 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 167
  (Polychromatic418967fa.accept_10_3_4_7_1_353 23 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 114 167 (accept_3_2 22 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 114 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 114 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 114 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 167 (accept_3_2 19 114 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 114 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 114 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 114 167 (accept_3_2 16 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 114 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 114 167 (Polychromatic418967fa.accept_13_1_10_11_1_1280 14 114 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 167 (accept_3_2 13 114 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 114 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 167
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 114 167 (accept_3_2 10 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  114 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 114 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 114 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 167 (accept_3_2 7 114 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 167 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 114 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 167 (accept_3_2 4 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  114 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 114 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 114 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 114 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 167 (accept_3_2 1 114 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 114 167)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 113 167
  (Eq.refl Bool.true) (allA_succ_of_accept 54 113 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 113 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 167
  (Polychromatic418967fa.accept_13_1_9_11_1_703 53 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 167 (accept_3_2 52 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 113 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 167 (accept_3_2 49 113 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 167 (Polychromatic418967fa.accept_22_4_3_13_1_7770 48 113 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 167
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 167 (accept_3_2 46 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 167 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 113 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 167 (accept_3_2 43 113 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 113 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 167
  (Polychromatic418967fa.accept_13_2_9_11_1_258 41 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 167 (accept_3_2 40 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 167 (Polychromatic418967fa.accept_15_9_8_2_1_1109 39 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 113 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 167 (accept_3_2 37 113 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 167 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 113 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 167
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 167 (accept_3_2 34 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 167 (Polychromatic418967fa.accept_21_11_8_20_1_4591 32 113 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 167 (accept_3_2 31 113 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 113 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 167
  (Polychromatic418967fa.accept_17_12_11_14_1_3120 29 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 113 167 (accept_3_2 28 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 113 167 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 113 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 113 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 167 (accept_3_2 25 113 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 167 (Polychromatic418967fa.accept_10_4_3_7_1_1110
  24 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 167
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 167 (accept_3_2 22 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 167 (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 167 (Polychromatic418967fa.accept_13_7_9_11_1_705 20 113 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 167 (accept_3_2 19 113 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 167
  (Polychromatic418967fa.accept_21_17_8_20_1_7805 17 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 113 167 (accept_3_2 16 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 113 167 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 113 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 167 (accept_3_2 13 113 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 167 (Polychromatic418967fa.accept_7_5_1_6_1_163
  12 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 167
  (Polychromatic418967fa.accept_21_11_8_20_1_4591 11 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 113 167 (accept_3_2 10 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 113 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 113 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 167 (Polychromatic418967fa.accept_13_8_9_11_1_1265 8 113
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 167 (accept_3_2 7 113 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 167
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 167 (accept_3_2 4 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 167 (Polychromatic418967fa.accept_17_3_11_14_1_2071 3 113 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 167 (accept_3_2 1 113 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 167))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 112 167
  (Eq.refl Bool.true) (allA_of_3_0 56 112 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 111 167 (Eq.refl
  Bool.true) (allA_succ_of_accept 56 111 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 167 (accept_3_2 55 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 167 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 111 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 167 (accept_3_2 52 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 167 (accept_3_2 49 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 167 (Polychromatic418967fa.accept_13_9_7_11_1_1292 48 111 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 167 (accept_3_2 46 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 167 (accept_3_2 43 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 111 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 167
  (Polychromatic418967fa.accept_15_11_6_2_1_1106 41 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 167 (accept_3_2 40 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 167 (Polychromatic418967fa.accept_17_5_9_14_1_4282 39 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 167 (accept_3_2 37 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 167 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 111 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 167 (accept_3_2 34 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 167 (accept_3_2 31 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 167 (Polychromatic418967fa.accept_13_4_7_11_1_1981 30 111 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 167 (accept_3_2 28 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 167 (Polychromatic418967fa.accept_13_1_7_11_1_702 27 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 167 (accept_3_2 25 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 111 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 167
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 23 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 167 (accept_3_2 22 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 167 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 167 (accept_3_2 19 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 167 (Polychromatic418967fa.accept_13_5_7_11_1_3470 18 111 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 167 (accept_3_2 16 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 167 (accept_3_2 13 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 167 (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 111 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 167 (accept_3_2 10 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 167 (accept_3_2 7 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 111 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 167
  (Polychromatic418967fa.accept_13_5_7_11_1_3470 5 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 167 (accept_3_2 4 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 167 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 111 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 167 (accept_3_2 1 111 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111 167))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 110 167
  (Eq.refl Bool.true) (allA_succ_of_accept 57 110 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 110 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 110 167
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 110 167 (accept_3_2 55 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 110 167 (Polychromatic418967fa.accept_25_4_10_17_1_9283 54 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 110 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 110 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 110 167 (accept_3_2 52 110 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 110 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 110 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 110 167
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 110 167 (accept_3_2 49 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 110 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 110 167 (Polychromatic418967fa.accept_13_8_6_11_1_1979 47 110 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 110 167 (accept_3_2 46 110 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 110 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 110 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 110 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 110 167 (accept_3_2 43 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 110 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 110 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 110 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 110 167 (accept_3_2 40 110 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 110 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 110 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 110 167
  (Polychromatic418967fa.accept_20_18_10_7_1_9245 38 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 110 167 (accept_3_2 37 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 110 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 110 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 110 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 110 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 110 167 (accept_3_2 34 110 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 110 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 110 167
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 110 167 (accept_3_2 31 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 110 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 110 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 110 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 110 167 (accept_3_2 28 110 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 110 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 110 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 110 167 (accept_3_2 25 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 110 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 110 167 (Polychromatic418967fa.accept_17_6_8_14_1_6706 23 110 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 167 (accept_3_2 22 110 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 110 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 110 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 110 167
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 110 167 (accept_3_2 19 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 110 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 110 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 167 (accept_3_2 16 110 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 110 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 110 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 110 167
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 110 167 (accept_3_2 13 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 110 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 110 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 110 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 110 167 (accept_3_2 10 110 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 110 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 167
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 110 167 (accept_3_2 7 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  110 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 110 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 110 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 110 167 (accept_3_2 4 110 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 110 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 167
  (Polychromatic418967fa.accept_21_2_5_20_1_7789 2 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 167 (accept_3_2 1 110 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 109 167 (Eq.refl Bool.true) (allA_of_3_0
  59 109 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 108 167 (Eq.refl Bool.true) (allA_succ_of_accept 59
  108 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 108 167 (accept_3_2 58 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 108 167 (Polychromatic418967fa.accept_15_12_3_2_1_2756 57 108 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 167 (Polychromatic418967fa.accept_16_8_12_7_1_2399 56 108
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 167 (accept_3_2 55 108
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 108 167
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 54 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 108 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 108 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 167 (accept_3_2 52 108 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 108 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 108 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 167 (Polychromatic418967fa.accept_15_5_3_2_1_5930
  50 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 167 (accept_3_2 49
  108 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 108 167
  (Polychromatic418967fa.accept_11_4_9_2_1_259 48 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 108 167 (Polychromatic418967fa.accept_13_8_4_11_1_3469 47 108 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 167 (accept_3_2 46 108 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 108 167 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 108 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 167
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 108 167 (accept_3_2 43 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 108 167 (Polychromatic418967fa.accept_15_12_3_2_1_2756 42 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 108 167 (Polychromatic418967fa.accept_13_2_4_11_1_2003 41 108 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 167 (accept_3_2 40 108 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 108 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 167
  (Polychromatic418967fa.accept_13_12_4_11_1_1925 38 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 108 167 (accept_3_2 37 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 108 167 (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 108 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 167 (Polychromatic418967fa.accept_8_3_4_7_1_475
  35 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 167 (accept_3_2 34
  108 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 167
  (Polychromatic418967fa.accept_13_7_4_11_1_1967 33 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 108 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 108 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 167 (accept_3_2 31 108 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 108 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 108 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 167 (Polychromatic418967fa.accept_10_9_8_7_1_714
  29 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 167 (accept_3_2 28
  108 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 167
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 108 167 (Polychromatic418967fa.accept_11_4_9_2_1_259 26 108 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 167 (accept_3_2 25 108 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 108 167 (Polychromatic418967fa.accept_16_8_12_7_1_2399 24 108 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 167
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 108 167 (accept_3_2 22 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 108 167 (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 108 167 (Polychromatic418967fa.accept_13_7_4_11_1_1967 20 108 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 167 (accept_3_2 19 108 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 108 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 167
  (Polychromatic418967fa.accept_14_3_10_13_1_339 17 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 108 167 (accept_3_2 16 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 108 167 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 108 167 (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 108 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 167 (accept_3_2 13 108 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 167 (Polychromatic418967fa.accept_13_12_4_11_1_1925 12 108
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 167
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 108 167 (accept_3_2 10 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  108 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 108 167 (Polychromatic418967fa.accept_13_8_4_11_1_3469 8 108 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 167 (accept_3_2 7 108 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 167 (Polychromatic418967fa.accept_13_6_4_11_1_282 6 108 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 167
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 167 (accept_3_2 4 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  108 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 108 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 108 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 108 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 167 (accept_3_2 1 108 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 108 167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 107
  167 (Eq.refl Bool.true) (allA_succ_of_accept 60 107 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 107 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 167
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 107 167 (accept_3_2 58 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 107 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 107 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 107 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 167 (accept_3_2 55 107 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 167 (Polychromatic418967fa.accept_13_2_3_11_1_1287 54 107 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 167
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 107 167 (accept_3_2 52 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 107 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 107 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 107 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 167 (accept_3_2 49 107 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 107 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 167 (accept_3_2 46 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 107 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 167 (accept_3_2 43 107 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 107 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 167
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 41 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 167 (accept_3_2 40 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 107 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 167 (accept_3_2 37 107 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 107 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 167
  (Polychromatic418967fa.accept_16_3_11_7_1_770 35 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 167 (accept_3_2 34 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 107 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 167 (accept_3_2 31 107 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 107 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 167
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 167 (accept_3_2 28 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 167 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 167 (Polychromatic418967fa.accept_17_9_5_14_1_4277 26 107 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 167 (accept_3_2 25 107 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 107 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 167
  (Polychromatic418967fa.accept_13_10_3_11_1_1923 23 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 107 167 (accept_3_2 22 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 107 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 107 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 107 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 167 (accept_3_2 19 107 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 167 (Polychromatic418967fa.accept_7_4_2_6_1_337
  18 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 167
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 167 (accept_3_2 16 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 167 (Polychromatic418967fa.accept_13_1_3_11_1_1289 14 107 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 167 (accept_3_2 13 107 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 107 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 167
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 167 (accept_3_2 10 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 167 (Polychromatic418967fa.accept_17_9_5_14_1_4277 9 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 107 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 167 (accept_3_2 7 107 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 107 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 167
  (Polychromatic418967fa.accept_11_5_8_2_1_588 5 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 167 (accept_3_2 4 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 107 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 107 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 167 (accept_3_2 1 107 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 167))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 106
  167 (Eq.refl Bool.true) (allA_of_3_0 62 106 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 105 167
  (Eq.refl Bool.true) (allA_succ_of_accept 62 105 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 105 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 167 (accept_3_2 61 105 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 167 (Polychromatic418967fa.accept_13_8_1_11_1_1284 60 105
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 167
  (Polychromatic418967fa.accept_11_4_6_2_1_51 59 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 167 (accept_3_2 58 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 105 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 105 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 105 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 167 (accept_3_2 55 105 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 105 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 167
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 167 (accept_3_2 52 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 105 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 105 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 105 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 167 (accept_3_2 49 105 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 105 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 167
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 167 (accept_3_2 46 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 105 167 (Polychromatic418967fa.accept_16_13_9_7_1_4532 45 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 105 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 167 (accept_3_2 43 105 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 105 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 167
  (Polychromatic418967fa.accept_19_3_10_15_1_9241 41 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 105 167 (accept_3_2 40 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 105 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 105 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 105 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 167 (accept_3_2 37 105 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 167
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 105 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 105 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 167 (accept_3_2 34 105 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 167 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 105 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 167 (accept_3_2 31 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 105 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 105 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 105 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 167 (accept_3_2 28 105 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 105 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 167 (accept_3_2 25 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 105 167 (Polychromatic418967fa.accept_16_8_9_7_1_768 24 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 167 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 105 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 167 (accept_3_2 22 105 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 105 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 167 (accept_3_2 19 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 105 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 105 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 105 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 167 (accept_3_2 16 105 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 167 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 105 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 167 (accept_3_2 13 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 105 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 105 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 105 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 167 (accept_3_2 10 105 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 167 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 105 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 167 (accept_3_2 7 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  105 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 167 (Polychromatic418967fa.accept_19_5_10_15_1_5076 5 105 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 167 (accept_3_2 4 105 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 105 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 167 (accept_3_2 1 105 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  167))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 104 167 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 104 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 104 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 104 167 (Polychromatic418967fa.accept_10_2_4_7_1_352 62 104
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 167 (accept_3_2 61 104
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 104 167
  (Polychromatic418967fa.accept_16_12_8_7_1_4530 60 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 104 167 (Polychromatic418967fa.accept_19_2_9_15_1_9238 59 104 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 104 167 (accept_3_2 58 104 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 104 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 104 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 104 167
  (Polychromatic418967fa.accept_17_5_2_14_1_4270 56 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 104 167 (accept_3_2 55 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 104 167 (Polychromatic418967fa.accept_14_12_6_13_1_3173 54 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 104 167 (Polychromatic418967fa.accept_10_3_4_7_1_353 53 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 104 167 (accept_3_2 52 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 104 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 104 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 104 167
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 104 167 (accept_3_2 49 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 104 167 (Polychromatic418967fa.accept_15_3_14_2_1_1888 48 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 104 167 (Polychromatic418967fa.accept_14_5_6_13_1_3145 47 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 104 167 (accept_3_2 46 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 104 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 104 167
  (Polychromatic418967fa.accept_16_12_8_7_1_4530 44 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 104 167 (accept_3_2 43 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 104 167 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 104 167 (Polychromatic418967fa.accept_10_1_4_7_1_374 41 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 104 167 (accept_3_2 40 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 104 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 104 167
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 104 167 (accept_3_2 37 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 104 167 (Polychromatic418967fa.accept_16_4_8_7_1_3396 36 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 104 167 (Polychromatic418967fa.accept_14_7_6_13_1_4111 35 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 104 167 (accept_3_2 34 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 104 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 104 167
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 104 167 (accept_3_2 31 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 104 167 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 104 167 (Polychromatic418967fa.accept_18_11_14_5_1_3951 29 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 104 167 (accept_3_2 28 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 104 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 104 167
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 104 167 (accept_3_2 25 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 104 167 (Polychromatic418967fa.accept_19_5_9_15_1_9239 24 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 104 167 (Polychromatic418967fa.accept_10_3_4_7_1_353 23 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 104 167 (accept_3_2 22 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 104 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 104 167
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 20 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 104 167 (accept_3_2 19 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 104 167 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 104 167 (Polychromatic418967fa.accept_16_1_8_7_1_3377 17 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 167 (accept_3_2 16 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 104 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 167
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 104 167 (accept_3_2 13 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 104 167 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 104 167 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 167 (accept_3_2 10 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 167
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 167 (accept_3_2 7 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 167 (Polychromatic418967fa.accept_19_6_9_15_1_3694 6 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 167 (Polychromatic418967fa.accept_14_5_6_13_1_3145 5 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 167 (accept_3_2 4 104 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 167
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 167 (accept_3_2 1 104 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 103 167 (Eq.refl Bool.true)
  (allA_of_3_0 65 103 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 102 167 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 102 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 102 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 167 (accept_3_2 64 102 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 102 167 (Polychromatic418967fa.accept_15_3_12_2_1_507 63 102 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 62 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 102 167 (accept_3_2 61 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 102 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 102 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 102 167 (accept_3_2 58 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 102 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 102 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 102 167 (accept_3_2 55 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 102 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 102 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 167 (accept_3_2 52 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 102 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 102 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 167
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 50 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 102 167 (accept_3_2 49 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 102 167 (Polychromatic418967fa.accept_15_3_12_2_1_507 48 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 102 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 167 (accept_3_2 46 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 102 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 167
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 102 167 (accept_3_2 43 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 102 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 102 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 167 (accept_3_2 40 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 102 167 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 102 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 167
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 102 167 (accept_3_2 37 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 102 167 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 102 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 167 (accept_3_2 34 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 167
  (Polychromatic418967fa.accept_19_13_7_15_1_5054 32 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 102 167 (accept_3_2 31 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 102 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 102 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 102 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 102 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 167 (accept_3_2 28 102 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 167 (Polychromatic418967fa.accept_18_9_12_5_1_864
  27 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 167
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 102 167 (accept_3_2 25 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 102 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 102 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 167 (accept_3_2 22 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 102 167 (accept_3_2 19 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 102 167 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 102 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 167 (accept_3_2 16 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 102 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 167
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 167 (accept_3_2 13 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 102 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 102 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 167 (accept_3_2 10 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 102 167 (accept_3_2 7 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  102 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 102 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 167 (accept_3_2 4 102 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 102 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 102 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 167
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 102 167 (accept_3_2 1 102 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 101 167 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 101 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 101 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 101 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 167 (accept_3_2 64 101 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 167
  (Polychromatic418967fa.accept_24_15_5_23_1_9282 63 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 101 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 167 (accept_3_2 61 101 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 101 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 167
  (Polychromatic418967fa.accept_16_11_5_7_1_2395 59 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 167 (accept_3_2 58 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 167 (Polychromatic418967fa.accept_10_6_1_7_1_342 56 101 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 167 (accept_3_2 55 101 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 101 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 167
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 167 (accept_3_2 52 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 101 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 167 (accept_3_2 49 101 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 101 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 167
  (Polychromatic418967fa.accept_13_8_10_11_1_2730 47 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 101 167 (accept_3_2 46 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 101 167 (Polychromatic418967fa.accept_17_11_16_14_1_6760 45 101 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 44
  101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 167 (accept_3_2 43
  101 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 101 167 (Polychromatic418967fa.accept_13_2_10_11_1_1276 41 101 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 167 (accept_3_2 40 101 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 101 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 167 (accept_3_2 37 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 167 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 101 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 167 (accept_3_2 34 101 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 101 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 167
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 167 (accept_3_2 31 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 167 (Polychromatic418967fa.accept_13_3_10_11_1_1293 29 101 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 167 (accept_3_2 28 101 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 167 (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 101
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 167 (accept_3_2 25 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 101 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 167 (accept_3_2 22 101 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 101 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 167
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 167 (accept_3_2 19 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 101 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 167 (accept_3_2 16 101 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 101 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 167 (accept_3_2 13 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 101 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 167 (accept_3_2 10 101 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 101 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 167 (accept_3_2 7 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 167 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 101 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 167 (accept_3_2 4 101 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 101 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 167 (accept_3_2 1 101 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  167))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 100 167 (Eq.refl Bool.true)
  (allA_of_3_0 68 100 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 99 167 (Eq.refl Bool.true)
  (allA_succ_of_accept 68 99 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 99 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 167 (accept_3_2 67 99 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 99 167 (Polychromatic418967fa.accept_13_1_8_11_1_724 66 99 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 65
  99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 167 (accept_3_2 64 99
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 167
  (Polychromatic418967fa.accept_14_7_1_13_1_357 63 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 99 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 167 (accept_3_2 61 99 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 99 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 167 (Polychromatic418967fa.accept_16_11_3_7_1_2375
  59 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 167 (accept_3_2 58
  99 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 167
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 99 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 167 (accept_3_2 55 99 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 99 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 99 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 167 (Polychromatic418967fa.accept_13_1_8_11_1_724
  53 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 167 (accept_3_2 52
  99 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 167
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 99 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 167 (accept_3_2 49 99 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 167 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 99 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 47
  99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 167 (accept_3_2 46 99
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 167
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 167 (accept_3_2 43 99 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 167 (Polychromatic418967fa.accept_10_2_9_7_1_720 42 99 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 167 (Polychromatic418967fa.accept_15_11_9_2_1_4780
  41 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 167 (accept_3_2 40
  99 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 167
  (Polychromatic418967fa.accept_19_1_4_15_1_2542 39 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 99 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 167 (accept_3_2 37 99 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 99 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 167 (Polychromatic418967fa.accept_13_9_8_11_1_725
  35 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 167 (accept_3_2 34
  99 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 167
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 167 (accept_3_2 31 99 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 99 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 167 (Polychromatic418967fa.accept_13_3_8_11_1_1906
  29 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 167 (accept_3_2 28
  99 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 167
  (Polychromatic418967fa.accept_13_1_8_11_1_724 27 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 99 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 167 (accept_3_2 25 99 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 167 (Polychromatic418967fa.accept_19_5_4_15_1_2512 24 99 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 167
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 167 (accept_3_2 22 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  99 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 167 (accept_3_2 19 99 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 167 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 99 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 167
  (Polychromatic418967fa.accept_13_4_8_11_1_1937 17 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 167 (accept_3_2 16 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 167 (Polychromatic418967fa.accept_16_15_3_7_1_3389 15 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 99 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 167 (accept_3_2 13 99 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 99 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 167
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 11 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 167 (accept_3_2 10 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 99 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 167 (accept_3_2 7 99 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 167 (Polychromatic418967fa.accept_13_6_8_11_1_5398 6 99 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 167
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 167 (accept_3_2 4 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99
  167 (Polychromatic418967fa.accept_13_3_8_11_1_1906 3 99 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 99 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 99 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 167 (accept_3_2 1 99 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 99 167))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  70 98 167 (Eq.refl Bool.true) (allA_succ_of_accept 69 98 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 98 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 167
  (Polychromatic418967fa.accept_12_8_2_11_1_246 68 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 167 (accept_3_2 67 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 167 (accept_3_2 64 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 98 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 167
  (Polychromatic418967fa.accept_20_2_18_7_1_3394 62 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 167 (accept_3_2 61 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 167 (Polychromatic418967fa.accept_10_9_8_7_1_714 59 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 167 (accept_3_2 58 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 98 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 167 (accept_3_2 55 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 167 (Polychromatic418967fa.accept_15_9_8_2_1_1109 54 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 167 (accept_3_2 52 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 98 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 167
  (Polychromatic418967fa.accept_18_14_8_5_1_860 50 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 167 (accept_3_2 49 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 167 (accept_3_2 46 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 98 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 167
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 167 (accept_3_2 43 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 167 (accept_3_2 40 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 98 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 167 (accept_3_2 37 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 167 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 167 (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 167 (accept_3_2 34 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 98 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 167
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 167 (accept_3_2 31 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 167 (accept_3_2 28 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 98 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 167
  (Polychromatic418967fa.accept_19_7_3_15_1_2428 26 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 167 (accept_3_2 25 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 167 (Polychromatic418967fa.accept_11_1_10_2_1_58 23 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 167 (accept_3_2 22 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 98 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 167 (accept_3_2 19 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 167 (Polychromatic418967fa.accept_13_5_7_11_1_3470 18 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 167 (accept_3_2 16 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 98 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 167
  (Polychromatic418967fa.accept_13_1_7_11_1_702 14 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 167 (accept_3_2 13 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 167 (accept_3_2 10 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 167
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 167 (accept_3_2 7 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  167 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 167 (accept_3_2 4 98 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 98 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  98 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 167 (accept_3_2 1 98 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 97 167 (Eq.refl Bool.true)
  (allA_of_3_0 71 97 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 96 167 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 96 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 96 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 96 167 (accept_3_2 70 96 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 96 167 (Polychromatic418967fa.accept_18_15_6_5_1_3972 69 96 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 167
  (Polychromatic418967fa.accept_13_3_5_11_1_716 68 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 96 167 (accept_3_2 67 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  96 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 96 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 96 167 (accept_3_2 64 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 96 167 (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 96 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 167
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 96 167 (accept_3_2 61 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  96 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 96 167 (Polychromatic418967fa.accept_13_7_5_11_1_1927 59 96 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 167 (accept_3_2 58 96 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 96 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 96 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 167
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 96 167 (accept_3_2 55 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  96 167 (Polychromatic418967fa.accept_17_3_11_14_1_2071 54 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 96 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 96 167 (accept_3_2 52 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 96 167 (Polychromatic418967fa.accept_10_1_6_7_1_710 51 96 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 167
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 96 167 (accept_3_2 49 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  96 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 96 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 96 167 (accept_3_2 46 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 96 167 (Polychromatic418967fa.accept_13_6_5_11_1_1971 45 96 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 167
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 96 167 (accept_3_2 43 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  96 167 (Polychromatic418967fa.accept_13_3_5_11_1_716 42 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 96 167 (Polychromatic418967fa.accept_10_1_6_7_1_710 41 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 167 (accept_3_2 40 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 96 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 96 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 167
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 96 167 (accept_3_2 37 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  96 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 96 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 167 (accept_3_2 34 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 96 167 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 96 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 167
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 96 167 (accept_3_2 31 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  96 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 96 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 167 (accept_3_2 28 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 96 167 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 96 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 167
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 96 167 (accept_3_2 25 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  96 167 (Polychromatic418967fa.accept_19_5_1_15_1_9264 24 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 96 167 (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 167 (accept_3_2 22 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 96 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 96 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 167
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 167 (accept_3_2 19 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  96 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 96 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 167 (accept_3_2 16 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 96 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 96 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 167
  (Polychromatic418967fa.accept_19_14_1_15_1_7914 14 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 96 167 (accept_3_2 13 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  96 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 96 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 167 (accept_3_2 10 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 96 167 (Polychromatic418967fa.accept_20_9_16_7_1_1129 9 96 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 167
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 96 167 (accept_3_2 7 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96
  167 (Polychromatic418967fa.accept_13_6_5_11_1_1971 6 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 96 167 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 167 (accept_3_2 4 96 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 96 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 96 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 167
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 96 167 (accept_3_2 1 96 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 95 167 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 95 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 95 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 167 (Polychromatic418967fa.accept_13_6_4_11_1_282 71 95 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 95 167 (accept_3_2 70 95 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 95 167
  (Polychromatic418967fa.accept_17_1_10_14_1_1173 69 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 95 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 95 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 167 (accept_3_2 67 95 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 95 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 95 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 65
  95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 95 167 (accept_3_2 64 95
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 167
  (Polychromatic418967fa.accept_10_3_5_7_1_330 63 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 95 167 (Polychromatic418967fa.accept_10_2_5_7_1_1124 62 95 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 167 (accept_3_2 61 95 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 95 167 (Polychromatic418967fa.accept_13_8_4_11_1_3469 60 95 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 167
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 167 (accept_3_2 58 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 167 (Polychromatic418967fa.accept_15_12_5_2_1_2786 57 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 167 (Polychromatic418967fa.accept_15_11_5_2_1_520 56 95 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 167 (accept_3_2 55 95 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 95 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 167
  (Polychromatic418967fa.accept_10_3_5_7_1_330 53 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 167 (accept_3_2 52 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 167 (Polychromatic418967fa.accept_20_10_15_7_1_6312 50 95 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 167 (accept_3_2 49 95 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 167 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 95 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 167
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 167 (accept_3_2 46 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 95 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 167 (accept_3_2 43 95 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 167 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 95 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 167
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 41 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 167 (accept_3_2 40 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 167 (Polychromatic418967fa.accept_17_5_10_14_1_2083 39 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 95 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 167 (accept_3_2 37 95 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 167 (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 95 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 167
  (Polychromatic418967fa.accept_16_3_15_7_1_3417 35 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 167 (accept_3_2 34 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 167 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 95 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 167 (accept_3_2 31 95 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 95 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 167
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 167 (accept_3_2 28 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 167 (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 95 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 167 (accept_3_2 25 95 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 95 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 167
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 167 (accept_3_2 22 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 167 (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 167 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 95 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 167 (accept_3_2 19 95 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 167 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 95 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 167
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 167 (accept_3_2 16 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 167 (Polychromatic418967fa.accept_13_2_4_11_1_2003 15 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 167 (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 95 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 167 (accept_3_2 13 95 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 95 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 167
  (Polychromatic418967fa.accept_15_11_5_2_1_520 11 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 167 (accept_3_2 10 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 167 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 95 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 167 (accept_3_2 7 95 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 167 (Polychromatic418967fa.accept_13_6_4_11_1_282 6 95 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 167
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 167 (accept_3_2 4 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  167 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 95 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 95 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 167 (accept_3_2 1 95 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95 167))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74
  94 167 (Eq.refl Bool.true) (allA_of_3_0 74 94 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 93 167
  (Eq.refl Bool.true) (allA_succ_of_accept 74 93 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 93 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 167 (accept_3_2 73 93 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 93 167 (Polychromatic418967fa.accept_15_12_3_2_1_2756 72 93
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 167
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 93 167 (accept_3_2 70 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  93 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 93 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 167 (accept_3_2 67 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 93 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 93 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 93 167 (accept_3_2 64 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  93 167 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 93 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 93 167 (accept_3_2 61 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 93 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 93 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 167
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 93 167 (accept_3_2 58 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  93 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 93 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 167 (accept_3_2 55 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 93 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 93 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 167
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 167 (accept_3_2 52 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  93 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 93 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 167 (accept_3_2 49 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 167 (Polychromatic418967fa.accept_13_9_2_11_1_1964 48 93 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 93 167 (accept_3_2 46 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  93 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 93 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 167 (accept_3_2 43 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 167
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 41 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 93 167 (accept_3_2 40 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  93 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 93 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 167 (accept_3_2 37 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 93 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 167 (accept_3_2 34 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  93 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 93 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 167 (accept_3_2 31 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 167
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 93 167 (accept_3_2 28 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  93 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 93 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 167 (accept_3_2 25 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 93 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 167
  (Polychromatic418967fa.accept_13_10_2_11_1_1920 23 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 167 (accept_3_2 22 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  93 167 (Polychromatic418967fa.accept_19_2_17_15_1_1377 21 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 93 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 167 (accept_3_2 19 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 167
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 167 (accept_3_2 16 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  93 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 93 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 167 (accept_3_2 13 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 167 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 93 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 167
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 167 (accept_3_2 10 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  93 167 (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 93 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 167 (accept_3_2 7 93 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 167
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 167 (accept_3_2 4 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93
  167 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 93 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 93 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 167 (accept_3_2 1 93 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 93 167))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76
  92 167 (Eq.refl Bool.true) (allA_succ_of_accept 75 92 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 92 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 167
  (Polychromatic418967fa.accept_10_4_2_7_1_373 74 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 167 (accept_3_2 73 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 167 (accept_3_2 70 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 92 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 167
  (Polychromatic418967fa.accept_7_5_1_6_1_163 68 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 167 (accept_3_2 67 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 167 (accept_3_2 64 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 62 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 167 (accept_3_2 61 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 167 (accept_3_2 58 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 167
  (Polychromatic418967fa.accept_16_8_12_7_1_2399 56 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 167 (accept_3_2 55 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 167 (accept_3_2 52 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 167
  (Polychromatic418967fa.accept_11_6_4_2_1_599 50 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 167 (accept_3_2 49 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 167 (accept_3_2 46 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 167
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 167 (accept_3_2 43 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 167 (Polychromatic418967fa.accept_19_3_16_15_1_9281 41 92 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 167 (accept_3_2 40 92 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 167
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 167 (accept_3_2 37 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 167 (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 167 (accept_3_2 34 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 167
  (Polychromatic418967fa.accept_19_13_16_15_1_3781 32 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 92 167 (accept_3_2 31 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 92 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 92 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 92 167 (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 92 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 167 (accept_3_2 28 92 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27
  92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 167
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 167 (accept_3_2 25 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 167 (accept_3_2 22 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 167
  (Polychromatic418967fa.accept_11_9_4_2_1_600 20 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 167 (accept_3_2 19 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 167 (Polychromatic418967fa.accept_16_2_12_7_1_3410 18 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 167 (accept_3_2 16 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 167
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 167 (accept_3_2 13 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 167 (accept_3_2 10 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 167 (accept_3_2 7 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  167 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 92 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 167 (accept_3_2 4 92 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  92 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 167 (accept_3_2 1 92 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 91 167 (Eq.refl
  Bool.true) (allA_of_3_0 77 91 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 90 167 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 90 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 90 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 90 167 (accept_3_2 76 90 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 90 167 (Polychromatic418967fa.accept_13_10_12_11_1_731 75 90 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 90 167
  (Polychromatic418967fa.accept_19_17_14_15_1_1403 74 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 90 167 (accept_3_2 73 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 90 167 (Polychromatic418967fa.accept_13_7_12_11_1_1911 72 90 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 90 167 (Polychromatic418967fa.accept_20_11_10_7_1_9280 71 90
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 90 167 (accept_3_2 70 90 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 90 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 69
  90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 90 167
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 68 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 90 167 (accept_3_2 67 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  90 167 (Polychromatic418967fa.accept_13_1_12_11_1_728 66 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 90 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 90 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 90 167 (accept_3_2 64 90 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 90 167 (Polychromatic418967fa.accept_14_7_6_13_1_4111 63 90 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 167
  (Polychromatic418967fa.accept_13_10_12_11_1_731 62 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 90 167 (accept_3_2 61 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  90 167 (Polychromatic418967fa.accept_17_9_5_14_1_4277 60 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 90 167 (Polychromatic418967fa.accept_13_7_12_11_1_1911 59 90 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 90 167 (accept_3_2 58 90 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 90 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 90 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 167
  (Polychromatic418967fa.accept_13_4_12_11_1_5362 56 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 90 167 (accept_3_2 55 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  90 167 (Polychromatic418967fa.accept_14_12_6_13_1_3173 54 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 90 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 90 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 167 (accept_3_2 52 90 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 90 167 (Polychromatic418967fa.accept_16_3_10_7_1_4518 51 90 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 90 167
  (Polychromatic418967fa.accept_23_4_21_6_1_9279 50 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 90 167 (accept_3_2 49 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  90 167 (Polychromatic418967fa.accept_19_10_14_15_1_2478 48 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 90 167 (Polychromatic418967fa.accept_14_5_6_13_1_3145 47 90 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 167 (accept_3_2 46 90 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 90 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 90 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 167
  (Polychromatic418967fa.accept_17_10_5_14_1_4203 44 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 90 167 (accept_3_2 43 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  90 167 (Polychromatic418967fa.accept_19_4_14_15_1_9231 42 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 90 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 90 167 (accept_3_2 40 90 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 90 167 (Polychromatic418967fa.accept_19_1_14_15_1_3704 39 90 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 167
  (Polychromatic418967fa.accept_20_18_10_7_1_9245 38 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 90 167 (accept_3_2 37 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  90 167 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 90 167 (Polychromatic418967fa.accept_14_7_6_13_1_4111 35 90 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 167 (accept_3_2 34 90 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 167
  (Polychromatic418967fa.accept_19_13_14_15_1_7924 32 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 90 167 (accept_3_2 31 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 90 167 (Polychromatic418967fa.accept_13_4_12_11_1_5362 30 90 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 90 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 167 (accept_3_2 28 90 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 90 167 (Polychromatic418967fa.accept_13_1_12_11_1_728
  27 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 167
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 26 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 90 167 (accept_3_2 25 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  90 167 (Polychromatic418967fa.accept_21_3_6_20_1_9278 24 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 90 167 (Polychromatic418967fa.accept_13_10_12_11_1_731 23 90 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 167 (accept_3_2 22 90 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 167
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 20 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 90 167 (accept_3_2 19 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  90 167 (Polychromatic418967fa.accept_19_18_14_15_1_9277 18 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 90 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 167 (accept_3_2 16 90 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 90 167 (Polychromatic418967fa.accept_20_15_10_7_1_7878 15 90 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 167
  (Polychromatic418967fa.accept_13_1_12_11_1_728 14 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 167 (accept_3_2 13 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  90 167 (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 90 167 (Polychromatic418967fa.accept_19_11_14_15_1_9276 11 90 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 167 (accept_3_2 10 90 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 90 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 167
  (Polychromatic418967fa.accept_20_8_10_7_1_6291 8 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 90 167 (accept_3_2 7 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90
  167 (Polychromatic418967fa.accept_24_6_18_23_1_9275 6 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 90 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 167 (accept_3_2 4 90 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 167 (Polychromatic418967fa.accept_16_3_10_7_1_4518 3 90 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 167
  (Polychromatic418967fa.accept_17_2_5_14_1_2068 2 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 167 (accept_3_2 1 90 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 89 167 (Eq.refl
  Bool.true) (allA_succ_of_accept 78 89 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 167 (Polychromatic418967fa.accept_16_13_9_7_1_4532
  77 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 89 167 (accept_3_2 76
  89 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 89 167
  (Polychromatic418967fa.accept_9_3_8_5_1_65 75 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 89 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 89 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 167 (accept_3_2 73 89 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 89 167 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 71
  89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 89 167 (accept_3_2 70 89
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 89 167
  (Polychromatic418967fa.accept_9_6_8_5_1_837 69 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 89 167 (Polychromatic418967fa.accept_10_8_9_7_1_1118 68 89 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 167 (accept_3_2 67 89 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 89 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 65
  89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 89 167 (accept_3_2 64 89
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 89 167
  (Polychromatic418967fa.accept_15_3_14_2_1_1888 63 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 89 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 89 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 167 (accept_3_2 61 89 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 89 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 167
  (Polychromatic418967fa.accept_19_2_13_15_1_9274 59 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 167 (accept_3_2 58 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 167 (accept_3_2 55 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 89 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 167
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 167 (accept_3_2 52 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 167 (accept_3_2 49 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 89 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 167 (accept_3_2 46 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 167 (Polychromatic418967fa.accept_16_13_9_7_1_4532 45 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 167 (Polychromatic418967fa.accept_18_8_17_5_1_9273 44 89 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 167 (accept_3_2 43 89 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 89 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 167
  (Polychromatic418967fa.accept_17_7_4_14_1_2106 41 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 167 (accept_3_2 40 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 167 (accept_3_2 37 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 89 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 167
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 167 (accept_3_2 34 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 167 (accept_3_2 31 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 167
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 167 (accept_3_2 28 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 167 (Polychromatic418967fa.accept_15_12_14_2_1_3794 27 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 167 (accept_3_2 25 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 89 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 167
  (Polychromatic418967fa.accept_19_4_13_15_1_3676 23 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 167 (accept_3_2 22 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 167 (accept_3_2 19 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 167
  (Polychromatic418967fa.accept_19_17_13_15_1_1402 17 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 89 167 (accept_3_2 16 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 89 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 89 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 167 (accept_3_2 13 89 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 12
  89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 167
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 167 (accept_3_2 10 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 167 (Polychromatic418967fa.accept_17_9_4_14_1_4302 9 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 167 (accept_3_2 7 89 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 167
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 167 (accept_3_2 4 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  167 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 89 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 167 (accept_3_2 1 89 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 88 167 (Eq.refl Bool.true) (allA_of_3_0 80 88 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  81 87 167 (Eq.refl Bool.true) (allA_succ_of_accept 80 87 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 87 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 167 (accept_3_2 79 87 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 87 167 (Polychromatic418967fa.accept_11_1_10_2_1_58
  78 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 167
  (Polychromatic418967fa.accept_19_1_11_15_1_2459 77 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 87 167 (accept_3_2 76 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  87 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 87 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 167 (accept_3_2 73 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 87 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 87 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 167
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 87 167 (accept_3_2 70 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  87 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 69 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 87 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 167 (accept_3_2 67 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 87 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 87 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 167
  (Polychromatic418967fa.accept_7_2_3_6_1_4 65 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 167 (accept_3_2 64 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  87 167 (Polychromatic418967fa.accept_15_3_12_2_1_507 63 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 87 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 167 (accept_3_2 61 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 87 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 87 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 167
  (Polychromatic418967fa.accept_13_7_9_11_1_705 59 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 87 167 (accept_3_2 58 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  87 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 87 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 167 (accept_3_2 55 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 167 (Polychromatic418967fa.accept_13_2_9_11_1_258 54 87 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 167
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 87 167 (accept_3_2 52 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  87 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 87 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 167 (accept_3_2 49 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 87 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 167
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 167 (accept_3_2 46 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  87 167 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 87 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 167 (accept_3_2 43 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 167 (Polychromatic418967fa.accept_18_6_15_5_1_6563 42 87 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 167
  (Polychromatic418967fa.accept_13_2_9_11_1_258 41 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 87 167 (accept_3_2 40 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  87 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 87 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 167 (accept_3_2 37 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 167 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 87 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 167
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 167 (accept_3_2 34 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  87 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 87 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 167 (accept_3_2 31 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 87 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 167
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 167 (accept_3_2 28 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 167 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 167 (accept_3_2 25 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 167 (Polychromatic418967fa.accept_14_10_3_13_1_1530 24 87 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 167
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 167 (accept_3_2 22 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 167 (accept_3_2 19 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 87 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 167
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 167 (accept_3_2 16 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 167 (Polychromatic418967fa.accept_13_2_9_11_1_258 15 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 167 (accept_3_2 13 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 87 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 167
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 167 (accept_3_2 10 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 167 (accept_3_2 7 87 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 87 167 (Polychromatic418967fa.accept_15_6_12_2_1_2803 6 87 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 167 (Polychromatic418967fa.accept_15_5_12_2_1_2820
  5 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 167 (accept_3_2 4 87
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 167 (Polychromatic418967fa.accept_9_3_6_5_1_63
  3 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 167 (accept_3_2 1 87 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  167))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 86 167 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 86 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 80
  86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 86 167 (accept_3_2 79 86
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 86 167 (Polychromatic418967fa.accept_7_1_2_6_1_55
  78 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 86 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 86 167 (accept_3_2 76 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  86 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 86 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 74 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 86 167 (accept_3_2 73 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 86 167 (Polychromatic418967fa.accept_17_4_1_14_1_4296 72 86 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 86 167
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 86 167 (accept_3_2 70 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  86 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 86 167 (Polychromatic418967fa.accept_12_8_2_11_1_246 68 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 86 167 (accept_3_2 67 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 86 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 86 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 86 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 86 167 (accept_3_2 64 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  86 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 86 167 (Polychromatic418967fa.accept_11_7_9_2_1_260 62 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 86 167 (accept_3_2 61 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 86 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 86 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 86 167
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 86 167 (accept_3_2 58 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  86 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 86 167 (Polychromatic418967fa.accept_12_8_2_11_1_246 56 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 86 167 (accept_3_2 55 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 86 167 (Polychromatic418967fa.accept_15_9_11_2_1_1882 54 86 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 86 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 86 167 (accept_3_2 52 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  86 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 86 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 86 167 (accept_3_2 49 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 86 167 (Polychromatic418967fa.accept_11_4_9_2_1_259 48 86 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 86 167
  (Polychromatic418967fa.accept_16_15_6_7_1_4512 47 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 86 167 (accept_3_2 46 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  86 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 86 167 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 86 167 (accept_3_2 43 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 86 167 (Polychromatic418967fa.accept_13_3_8_11_1_1906 42 86 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 86 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 86 167 (accept_3_2 40 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  86 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 86 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 86 167 (accept_3_2 37 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 86 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 86 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 86 167
  (Polychromatic418967fa.accept_13_9_8_11_1_725 35 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 86 167 (accept_3_2 34 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  86 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 86 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 86 167 (accept_3_2 31 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 86 167 (Polychromatic418967fa.accept_13_4_8_11_1_1937 30 86 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 86 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 86 167 (accept_3_2 28 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  86 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 86 167 (Polychromatic418967fa.accept_11_4_9_2_1_259 26 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 86 167 (accept_3_2 25 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 86 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 86 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 86 167
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 86 167 (accept_3_2 22 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  86 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 86 167 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 86 167 (accept_3_2 19 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 86 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 86 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 86 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 86 167 (accept_3_2 16 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  86 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 86 167 (Polychromatic418967fa.accept_13_1_8_11_1_724 14 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 86 167 (accept_3_2 13 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 86 167 (Polychromatic418967fa.accept_20_12_6_7_1_7875 12 86 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 86 167
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 86 167 (accept_3_2 10 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  86 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 86 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 86 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 86 167 (accept_3_2 7 86 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 86 167 (Polychromatic418967fa.accept_13_6_8_11_1_5398 6 86 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 86 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 167 (accept_3_2 4 86 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 86 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 86
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 167
  (Polychromatic418967fa.accept_23_2_17_6_1_9272 2 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 86 167 (accept_3_2 1 86 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 85 167 (Eq.refl
  Bool.true) (allA_of_3_0 83 85 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 167 (allA_succ_of_accept 83
  84 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 83 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 84 167 (accept_3_2 82 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 84 167 (Polychromatic418967fa.accept_10_1_4_7_1_374 81 84 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 84 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 80 84 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 167 (accept_3_2 79 84 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 78
  84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 84 167
  (Polychromatic418967fa.accept_16_13_4_7_1_1537 77 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 84 167 (accept_3_2 76 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  84 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 84 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 74 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 167 (accept_3_2 73 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 167 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 84 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 84 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 71 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 167 (accept_3_2 70 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  84 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 84 167 (Polychromatic418967fa.accept_15_8_9_2_1_1897 68 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 167 (accept_3_2 67 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 167 (Polychromatic418967fa.accept_17_15_16_14_1_4291 66 84 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 167 (accept_3_2 64 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  84 167 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 84 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 62 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 167 (accept_3_2 61 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 84 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 167
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 167 (accept_3_2 58 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  84 167 (Polychromatic418967fa.accept_13_5_6_11_1_1933 57 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 84 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 167 (accept_3_2 55 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 167 (Polychromatic418967fa.accept_19_16_8_15_1_6447 54 84 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 167 (accept_3_2 52 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  84 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 84 167 (Polychromatic418967fa.accept_19_12_8_15_1_5067 50 84 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 167 (accept_3_2 49 84 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 167 (Polychromatic418967fa.accept_26_22_6_11_1_9271 48 84
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 167 (accept_3_2 46 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  84 167 (Polychromatic418967fa.accept_16_13_4_7_1_1537 45 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 84 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 167 (accept_3_2 43 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 84 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 167
  (Polychromatic418967fa.accept_10_1_4_7_1_374 41 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 167 (accept_3_2 40 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  84 167 (Polychromatic418967fa.accept_19_1_8_15_1_3786 39 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 84 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 167 (accept_3_2 37 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 167 (Polychromatic418967fa.accept_17_2_16_14_1_2116 36 84 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 167
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 167 (accept_3_2 34 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  84 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 84 167 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 167 (accept_3_2 31 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 167 (Polychromatic418967fa.accept_13_4_6_11_1_2017 30 84 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 167 (accept_3_2 28 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  84 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 84 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 167 (accept_3_2 25 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 84 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 167
  (Polychromatic418967fa.accept_10_3_4_7_1_353 23 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 167 (accept_3_2 22 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  84 167 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 84 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 167 (accept_3_2 19 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 167 (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 84 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 167 (accept_3_2 16 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 84 167 (Polychromatic418967fa.accept_16_14_4_7_1_2380 14 84 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 167 (accept_3_2 13 84 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 167 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 84 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 167
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 167 (accept_3_2 10 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 167 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 167 (accept_3_2 7 84 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 84 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 167
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 5 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 167 (accept_3_2 4 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  167 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 84 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 84 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 84 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 167 (accept_3_2 1 84 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 167))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 83 167 (allA_succ_of_accept 82 83 167 (accept_3_2 82 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 83 167 (Polychromatic418967fa.accept_11_4_6_2_1_51 81 83 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 83 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 83 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 167 (accept_3_2 79 83 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 78
  83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 167
  (Polychromatic418967fa.accept_22_11_17_13_1_9270 77 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 83 167 (accept_3_2 76 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 83 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 75 83 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 83 167 (Polychromatic418967fa.accept_10_4_3_7_1_1110 74 83 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 167 (accept_3_2 73 83 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 167 (Polychromatic418967fa.accept_13_7_5_11_1_1927
  72 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 167 (accept_3_2 70 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 68 83 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 167 (accept_3_2 67 83 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 83 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 167
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 65 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 167 (accept_3_2 64 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 167 (Polychromatic418967fa.accept_16_15_3_7_1_3389 63 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 83 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 167 (accept_3_2 61 83 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 83 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 167
  (Polychromatic418967fa.accept_11_4_6_2_1_51 59 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 167 (accept_3_2 58 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 167 (Polychromatic418967fa.accept_10_6_3_7_1_2197 56 83 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 167 (accept_3_2 55 83 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 167 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 83 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 167 (accept_3_2 52 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 167 (Polychromatic418967fa.accept_17_16_15_14_1_6747 50 83 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 167 (accept_3_2 49 83 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 83 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 167
  (Polychromatic418967fa.accept_16_15_3_7_1_3389 47 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 167 (accept_3_2 46 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 167 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 83 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 167 (accept_3_2 43 83 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 83 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 167
  (Polychromatic418967fa.accept_16_9_3_7_1_6883 41 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 167 (accept_3_2 40 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 167 (Polychromatic418967fa.accept_23_15_14_6_1_9269 38 83 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 167 (accept_3_2 37 83 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 83 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 167 (accept_3_2 34 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 167 (Polychromatic418967fa.accept_13_6_5_11_1_1971 32 83 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 167 (accept_3_2 31 83 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 83 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 167
  (Polychromatic418967fa.accept_13_3_5_11_1_716 29 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 167 (accept_3_2 28 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 167 (Polychromatic418967fa.accept_16_11_3_7_1_2375 27 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 83 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 167 (accept_3_2 25 83 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 83 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 167
  (Polychromatic418967fa.accept_17_6_15_14_1_8027 23 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 167 (accept_3_2 22 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 83 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 167 (accept_3_2 19 83 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 167 (Polychromatic418967fa.accept_19_18_7_15_1_3733 18 83 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 167 (accept_3_2 16 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 167 (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 83 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 167 (accept_3_2 13 83 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 83 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 167
  (Polychromatic418967fa.accept_16_11_3_7_1_2375 11 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 167 (accept_3_2 10 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 167 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 83 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 167 (accept_3_2 7 83 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 83 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 167
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 167 (accept_3_2 4 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  167 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 83 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 167 (Polychromatic418967fa.accept_24_2_11_23_1_9268 2 83 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 167 (accept_3_2 1 83 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 167 (allA_of_3_0 82 82 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 167
  (allA_succ_of_accept 80 81 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 81 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 167 (accept_3_2 79 81 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 167 (Polychromatic418967fa.accept_19_1_5_15_1_3722
  77 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 167 (accept_3_2 76
  81 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 167
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 81 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 167 (accept_3_2 73 81 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 167 (Polychromatic418967fa.accept_15_11_6_2_1_1106
  71 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 167 (accept_3_2 70
  81 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 167
  (Polychromatic418967fa.accept_17_1_13_14_1_478 69 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 167 (accept_3_2 67 81 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 65
  81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 167 (accept_3_2 64 81
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 167
  (Polychromatic418967fa.accept_12_3_9_11_1_231 63 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 81 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 167 (accept_3_2 61 81 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 167 (Polychromatic418967fa.accept_13_8_3_11_1_3467 60 81 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 167
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 167 (accept_3_2 58 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  81 167 (Polychromatic418967fa.accept_13_5_3_11_1_1288 57 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 81 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 167 (accept_3_2 55 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 167
  (Polychromatic418967fa.accept_11_9_4_2_1_600 53 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 167 (accept_3_2 52 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 167 (accept_3_2 49 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 167 (Polychromatic418967fa.accept_18_12_9_5_1_2771 48 81 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 167
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 167 (accept_3_2 46 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 167 (accept_3_2 43 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 167
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 41 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 167 (accept_3_2 40 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 167 (Polychromatic418967fa.accept_11_6_4_2_1_599 39 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 167 (accept_3_2 37 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 167 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 81 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 167
  (Polychromatic418967fa.accept_17_1_13_14_1_478 35 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 167 (accept_3_2 34 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 167 (accept_3_2 31 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 167
  (Polychromatic418967fa.accept_19_10_5_15_1_6443 29 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 167 (accept_3_2 28 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 167 (accept_3_2 25 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 81 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 167
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 167 (accept_3_2 22 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 167 (Polychromatic418967fa.accept_13_8_3_11_1_3467 21 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 167 (accept_3_2 19 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 167
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 167 (accept_3_2 16 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 167 (accept_3_2 13 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 81 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 167
  (Polychromatic418967fa.accept_15_11_6_2_1_1106 11 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 167 (accept_3_2 10 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 167 (accept_3_2 7 81 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 167
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 167 (accept_3_2 4 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  167 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 81 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 167 (accept_3_2 1 81 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 167 (allA_succ_of_accept 79 80 167 (accept_3_2 79 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 80 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 80 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 80 167 (Polychromatic418967fa.accept_17_9_12_14_1_5423 77 80
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 167 (accept_3_2 76 80 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 75
  80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 167
  (Polychromatic418967fa.accept_7_4_3_6_1_340 74 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 167 (accept_3_2 73 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 167 (Polychromatic418967fa.accept_15_11_5_2_1_520 71 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 167 (accept_3_2 70 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 167
  (Polychromatic418967fa.accept_13_3_2_11_1_1999 68 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 167 (accept_3_2 67 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 167 (accept_3_2 64 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 167
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 167 (accept_3_2 61 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 167 (Polychromatic418967fa.accept_14_3_10_13_1_339 59 80 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 167 (accept_3_2 58 80 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 167 (accept_3_2 55 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 167 (Polychromatic418967fa.accept_25_4_5_17_1_9267 54 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 167 (accept_3_2 52 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 167
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 167 (accept_3_2 49 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 167 (accept_3_2 46 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 167
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 167 (accept_3_2 43 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 167 (Polychromatic418967fa.accept_15_11_5_2_1_520 41 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 167 (accept_3_2 40 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 167 (accept_3_2 37 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 167 (Polychromatic418967fa.accept_13_10_2_11_1_1920 36 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 167 (Polychromatic418967fa.accept_13_9_2_11_1_1964 35 80 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 167 (accept_3_2 34 80 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 167
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 167 (accept_3_2 31 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 167 (accept_3_2 28 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 167
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 167 (accept_3_2 25 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 167 (accept_3_2 22 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 167 (accept_3_2 19 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 167 (Polychromatic418967fa.accept_13_4_2_11_1_733 17 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 167 (accept_3_2 16 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 167
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 167 (accept_3_2 13 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 167 (accept_3_2 10 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 167
  (Polychromatic418967fa.accept_19_8_4_15_1_1414 8 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 167 (accept_3_2 7 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  167 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 80 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 167 (Polychromatic418967fa.accept_19_5_4_15_1_2512 5 80 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 167 (accept_3_2 4 80 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 80
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 167 (accept_3_2 1 80 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 167 (allA_of_3_0 79
  79 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 167 (allA_succ_of_accept 77 78 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 167 (accept_3_2 76 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  78 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 78 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 167 (accept_3_2 73 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 78 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 167
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 167 (accept_3_2 70 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 167 (accept_3_2 67 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 78 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 167 (accept_3_2 64 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 167 (Polychromatic418967fa.accept_14_7_8_13_1_3161 63 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 62 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 167 (accept_3_2 61 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 167 (Polychromatic418967fa.accept_21_18_15_20_1_6076 60 78 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 167
  (Polychromatic418967fa.accept_10_9_8_7_1_714 59 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 167 (accept_3_2 58 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 167 (accept_3_2 55 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 78 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 167 (accept_3_2 52 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  78 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 167 (Polychromatic418967fa.accept_15_5_3_2_1_5930 50 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 167 (accept_3_2 49 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 78 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 167
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 167 (accept_3_2 46 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 167 (accept_3_2 43 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 167 (Polychromatic418967fa.accept_15_12_3_2_1_2756 42 78 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 167 (accept_3_2 40 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 167 (accept_3_2 37 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 167 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 78 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 167
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 167 (accept_3_2 34 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 167 (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 78 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 167 (accept_3_2 31 78 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 78 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 167 (accept_3_2 28 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 167 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 167 (accept_3_2 25 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 167 (Polychromatic418967fa.accept_17_7_10_14_1_8022 24 78 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 167
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 167 (accept_3_2 22 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 167 (accept_3_2 19 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 167 (Polychromatic418967fa.accept_17_1_10_14_1_1173 18 78 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 167 (accept_3_2 16 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 167 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 167 (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 167 (accept_3_2 13 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 78 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 167
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 167 (accept_3_2 10 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 78 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 167 (accept_3_2 7 78 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 78 167 (Polychromatic418967fa.accept_19_6_2_15_1_9266 6 78 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 167 (accept_3_2 4 78 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 78
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 167
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 167 (accept_3_2 1 78 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 167
  (allA_succ_of_accept 76 77 167 (accept_3_2 76 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 167 (Polychromatic418967fa.accept_13_10_12_11_1_731 75 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 77 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 167 (accept_3_2 73 77 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 167 (Polychromatic418967fa.accept_13_7_12_11_1_1911 72 77 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 167
  (Polychromatic418967fa.accept_14_1_7_13_1_333 71 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 167 (accept_3_2 70 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 167 (Polychromatic418967fa.accept_13_4_12_11_1_5362 69 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 167 (Polychromatic418967fa.accept_16_4_13_7_1_4522 68 77 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 167 (accept_3_2 67 77 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 77 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 167
  (Polychromatic418967fa.accept_19_8_1_15_1_2496 65 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 167 (accept_3_2 64 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 167 (Polychromatic418967fa.accept_17_12_9_14_1_4283 63 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 77 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 167 (accept_3_2 61 77 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 167 (Polychromatic418967fa.accept_21_18_14_20_1_9251 60 77 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 167
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 59 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 167 (accept_3_2 58 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 167 (Polychromatic418967fa.accept_14_1_7_13_1_333 57 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 167 (Polychromatic418967fa.accept_13_4_12_11_1_5362 56 77 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 167 (accept_3_2 55 77 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 77 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 167
  (Polychromatic418967fa.accept_13_1_12_11_1_728 53 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 167 (accept_3_2 52 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 167 (Polychromatic418967fa.accept_21_9_14_20_1_4579 51 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 77 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 167 (accept_3_2 49 77 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 167 (Polychromatic418967fa.accept_14_6_7_13_1_3158 48 77 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 167
  (Polychromatic418967fa.accept_21_5_14_20_1_9265 47 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 167 (accept_3_2 46 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 167 (Polychromatic418967fa.accept_24_21_5_23_1_7408 45 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 167 (Polychromatic418967fa.accept_20_4_17_7_1_3393 44 77 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 167 (accept_3_2 43 77 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 77 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 167
  (Polychromatic418967fa.accept_16_9_13_7_1_1509 41 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 167 (accept_3_2 40 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 167 (Polychromatic418967fa.accept_17_5_9_14_1_4282 39 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 167 (accept_3_2 37 77 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 167 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 77 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 167
  (Polychromatic418967fa.accept_19_16_1_15_1_6416 35 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 167 (accept_3_2 34 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 167 (Polychromatic418967fa.accept_13_7_12_11_1_1911 33 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 167 (Polychromatic418967fa.accept_20_12_17_7_1_4786 32 77 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 167 (accept_3_2 31 77 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 167
  (Polychromatic418967fa.accept_14_1_7_13_1_333 29 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 167 (accept_3_2 28 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 167 (Polychromatic418967fa.accept_13_1_12_11_1_728 27 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 167 (accept_3_2 25 77 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 167 (Polychromatic418967fa.accept_19_5_1_15_1_9264 24 77 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 167
  (Polychromatic418967fa.accept_13_10_12_11_1_731 23 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 167 (accept_3_2 22 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 167 (Polychromatic418967fa.accept_17_4_9_14_1_5406 21 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 167 (Polychromatic418967fa.accept_13_7_12_11_1_1911 20 77 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 167 (accept_3_2 19 77 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 167
  (Polychromatic418967fa.accept_13_4_12_11_1_5362 17 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 167 (accept_3_2 16 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 167 (Polychromatic418967fa.accept_14_1_7_13_1_333 15 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 167 (accept_3_2 13 77 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 167 (Polychromatic418967fa.accept_17_12_9_14_1_4283 12 77 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 167
  (Polychromatic418967fa.accept_19_11_1_15_1_9263 11 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 167 (accept_3_2 10 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 167 (Polychromatic418967fa.accept_16_9_13_7_1_1509 9 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 167 (Polychromatic418967fa.accept_14_8_7_13_1_4113 8 77 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 167 (accept_3_2 7 77 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 167
  (Polychromatic418967fa.accept_17_5_9_14_1_4282 5 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 167 (accept_3_2 4 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  167 (Polychromatic418967fa.accept_22_3_11_13_1_9262 3 77 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 77 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 167 (accept_3_2 1 77 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 77 167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 76 167 (allA_of_3_0 76 76 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 167
  (allA_succ_of_accept 74 75 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 75 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 167 (accept_3_2 73 75 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 75 167 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 71
  75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 167 (accept_3_2 70 75
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 167
  (Polychromatic418967fa.accept_9_6_3_5_1_240 69 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 75 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 167 (accept_3_2 67 75 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 75 167 (Polychromatic418967fa.accept_13_1_10_11_1_1280 66 75 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 75 167 (accept_3_2 64 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  75 167 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 75 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 167 (accept_3_2 61 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 75 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 75 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 167
  (Polychromatic418967fa.accept_11_4_9_2_1_259 59 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 75 167 (accept_3_2 58 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  75 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 75 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 167 (accept_3_2 55 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 167 (Polychromatic418967fa.accept_13_2_10_11_1_1276 54 75 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 167
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 167 (accept_3_2 52 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  75 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 75 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 167 (accept_3_2 49 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 167 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 75 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 167 (accept_3_2 46 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  75 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 75 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 167 (accept_3_2 43 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 75 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 167
  (Polychromatic418967fa.accept_13_2_10_11_1_1276 41 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 75 167 (accept_3_2 40 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  75 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 75 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 167 (accept_3_2 37 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 75 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 167 (accept_3_2 34 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  75 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 75 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 167 (accept_3_2 31 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 167 (Polychromatic418967fa.accept_13_4_10_11_1_1908 30 75 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 167
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 75 167 (accept_3_2 28 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  75 167 (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 75 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 167 (accept_3_2 25 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 75 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 167
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 167 (accept_3_2 22 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  75 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 75 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 167 (accept_3_2 19 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 75 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 167 (accept_3_2 16 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  75 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 75 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 167 (accept_3_2 13 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 75 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 167
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 167 (accept_3_2 10 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  75 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 75 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 167 (accept_3_2 7 75 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 75 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 167
  (Polychromatic418967fa.accept_16_5_11_7_1_5635 5 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 167 (accept_3_2 4 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75
  167 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 75 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 75 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 75 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 167 (accept_3_2 1 75 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 75 167))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74
  167 (allA_succ_of_accept 73 74 167 (accept_3_2 73 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 74 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 74 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 167 (accept_3_2 70 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 74 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 74 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 167
  (Polychromatic418967fa.accept_7_5_4_6_1_167 68 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 74 167 (accept_3_2 67 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  74 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 74 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 167 (accept_3_2 64 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 74 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 74 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 62 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 74 167 (accept_3_2 61 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  74 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 74 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 167 (accept_3_2 58 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 74 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 167
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 167 (accept_3_2 55 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 167 (accept_3_2 52 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 74 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 167
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 50 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 167 (accept_3_2 49 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 167 (accept_3_2 46 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 167
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 167 (accept_3_2 43 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 167 (accept_3_2 40 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 74 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 167
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 167 (accept_3_2 37 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 167 (Polychromatic418967fa.accept_29_7_16_22_1_9261 36 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 167 (accept_3_2 34 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 167
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 167 (accept_3_2 31 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 167 (accept_3_2 28 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 74 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 167
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 167 (accept_3_2 25 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 167 (accept_3_2 22 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 167
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 167 (accept_3_2 19 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 167 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 167 (accept_3_2 16 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 74 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 167
  (Polychromatic418967fa.accept_13_1_9_11_1_703 14 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 167 (accept_3_2 13 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 167 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 167 (accept_3_2 10 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 167 (accept_3_2 7 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  167 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 167 (accept_3_2 4 74 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 74 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  74 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 167 (accept_3_2 1 74 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 167 (allA_of_3_0 73 73 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 167 (allA_succ_of_accept 71 72 167
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 167 (accept_3_2 70 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 167 (Polychromatic418967fa.accept_10_9_2_7_1_1096 69 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 167 (Polychromatic418967fa.accept_13_3_7_11_1_1904 68 72 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 167 (accept_3_2 67 72 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 72 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 167
  (Polychromatic418967fa.accept_10_5_2_7_1_345 65 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 167 (accept_3_2 64 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 167 (Polychromatic418967fa.accept_15_3_12_2_1_507 63 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 167 (Polychromatic418967fa.accept_20_2_12_7_1_4799 62 72 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 167 (accept_3_2 61 72 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 72 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 167
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 167 (accept_3_2 58 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 167 (Polychromatic418967fa.accept_13_4_7_11_1_1981 56 72 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 167 (accept_3_2 55 72 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 167 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 72 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 167
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 167 (accept_3_2 52 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 167 (Polychromatic418967fa.accept_13_12_7_11_1_1935 51 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 72 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 167 (accept_3_2 49 72 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 167 (Polychromatic418967fa.accept_11_4_6_2_1_51 48 72 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 167
  (Polychromatic418967fa.accept_16_15_8_7_1_3407 47 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 167 (accept_3_2 46 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 167 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 72 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 167 (accept_3_2 43 72 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 167 (Polychromatic418967fa.accept_13_3_7_11_1_1904 42 72 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 167
  (Polychromatic418967fa.accept_16_9_8_7_1_4529 41 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 167 (accept_3_2 40 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 72 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 167 (accept_3_2 37 72 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 72 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 167
  (Polychromatic418967fa.accept_10_5_2_7_1_345 35 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 167 (accept_3_2 34 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 167 (Polychromatic418967fa.accept_15_3_12_2_1_507 33 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 72 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 167 (accept_3_2 31 72 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 167 (Polychromatic418967fa.accept_13_4_7_11_1_1981 30 72 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 167
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 167 (accept_3_2 28 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 167 (Polychromatic418967fa.accept_13_1_7_11_1_702 27 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 167 (Polychromatic418967fa.accept_11_4_6_2_1_51 26 72 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 167 (accept_3_2 25 72 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 72 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 167
  (Polychromatic418967fa.accept_21_2_9_20_1_9260 23 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 167 (accept_3_2 22 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 167 (Polychromatic418967fa.accept_15_6_12_2_1_2803 21 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 167 (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 72 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 167 (accept_3_2 19 72 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 72 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 167
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 167 (accept_3_2 16 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 167 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 72 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 167 (accept_3_2 13 72 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 167 (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 72 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 167
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 167 (accept_3_2 10 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 167 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 72 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 167 (accept_3_2 7 72 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 167 (Polychromatic418967fa.accept_15_6_12_2_1_2803 6 72 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 167
  (Polychromatic418967fa.accept_10_5_2_7_1_345 5 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 167 (accept_3_2 4 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  167 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 72 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 167 (Polychromatic418967fa.accept_20_2_12_7_1_4799 2 72 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 167 (accept_3_2 1 72 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 167
  (allA_succ_of_accept 70 71 167 (accept_3_2 70 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 69 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 71 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 167 (accept_3_2 67 71 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 71 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 167
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 167 (accept_3_2 64 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 167 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 167 (Polychromatic418967fa.accept_17_11_3_14_1_6736 62 71 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 167 (accept_3_2 61 71 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 71 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 167
  (Polychromatic418967fa.accept_21_17_8_20_1_7805 59 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 167 (accept_3_2 58 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 71 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 167 (accept_3_2 55 71 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 71 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 167
  (Polychromatic418967fa.accept_17_2_3_14_1_8043 53 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 167 (accept_3_2 52 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 167 (Polychromatic418967fa.accept_15_5_11_2_1_1095 50 71 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 167 (accept_3_2 49 71 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 71 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 167
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 167 (accept_3_2 46 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 167 (Polychromatic418967fa.accept_17_11_3_14_1_6736 45 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 71 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 167 (accept_3_2 43 71 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 71 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 167
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 41 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 167 (accept_3_2 40 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 71 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 167 (accept_3_2 37 71 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 167 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 71 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 167
  (Polychromatic418967fa.accept_14_7_1_13_1_357 35 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 167 (accept_3_2 34 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 167 (Polychromatic418967fa.accept_17_15_3_14_1_4230 32 71 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 167 (accept_3_2 31 71 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 71 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 167 (accept_3_2 28 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 167 (Polychromatic418967fa.accept_23_4_2_6_1_9259 27 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 71 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 167 (accept_3_2 25 71 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 71 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 167
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 167 (accept_3_2 22 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 71 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 167 (accept_3_2 19 71 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 167 (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 71 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 167
  (Polychromatic418967fa.accept_13_4_6_11_1_2017 17 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 167 (accept_3_2 16 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 167 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 71 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 167 (accept_3_2 13 71 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 71 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 167 (accept_3_2 10 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 167 (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 71 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 167 (accept_3_2 7 71 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 71 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 167
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 167 (accept_3_2 4 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  167 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 71 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 71 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 167 (accept_3_2 1 71 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 167))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 167
  (allA_of_3_0 70 70 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 167 (allA_succ_of_accept 68 69 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 167 (accept_3_2 67 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 167 (accept_3_2 64 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 69 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 167 (accept_3_2 61 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 167 (Polychromatic418967fa.accept_13_8_4_11_1_3469 60 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 167 (Polychromatic418967fa.accept_13_7_4_11_1_1967 59 69 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 167 (accept_3_2 58 69 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 69 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 167 (accept_3_2 55 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 167 (accept_3_2 52 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 69 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 167 (accept_3_2 49 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 167 (accept_3_2 46 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 167 (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 69 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 167 (accept_3_2 43 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 167 (Polychromatic418967fa.accept_13_2_4_11_1_2003 41 69 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 167 (accept_3_2 40 69 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 69 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 167 (accept_3_2 37 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 167 (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 167 (accept_3_2 34 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 167 (Polychromatic418967fa.accept_13_7_4_11_1_1967 33 69 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 167 (accept_3_2 31 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 167 (accept_3_2 28 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 69 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 167 (accept_3_2 25 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 167 (Polychromatic418967fa.accept_18_6_15_5_1_6563 24 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 167 (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 167 (accept_3_2 22 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 167 (accept_3_2 19 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 167 (accept_3_2 16 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 69 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 167 (accept_3_2 13 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 167 (accept_3_2 10 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 167 (Polychromatic418967fa.accept_18_9_15_5_1_6551 9 69 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 167 (accept_3_2 7 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 167 (Polychromatic418967fa.accept_19_5_12_15_1_9244 5 69 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 167 (accept_3_2 4 69 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 69 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 167 (accept_3_2 1 69 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  167))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 167 (allA_succ_of_accept 67 68
  167 (accept_3_2 67 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 167
  (Polychromatic418967fa.accept_13_1_3_11_1_1289 66 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 167 (Polychromatic418967fa.accept_10_5_8_7_1_2174 65 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 167 (accept_3_2 64 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 167 (Polychromatic418967fa.accept_12_2_8_11_1_31
  62 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 167 (accept_3_2 61
  68 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 167
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 167 (accept_3_2 58 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 167 (Polychromatic418967fa.accept_16_8_4_7_1_3390
  56 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 167 (accept_3_2 55
  68 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 167
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 54 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 167 (accept_3_2 52 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 68 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 50
  68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 167 (accept_3_2 49 68
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 167
  (Polychromatic418967fa.accept_14_6_12_13_1_3180 48 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 68 167 (Polychromatic418967fa.accept_13_8_3_11_1_3467 47 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 167 (accept_3_2 46 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 68 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 167 (Polychromatic418967fa.accept_13_5_3_11_1_1288
  44 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 167 (accept_3_2 43
  68 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 167
  (Polychromatic418967fa.accept_19_4_11_15_1_3743 42 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 68 167 (Polychromatic418967fa.accept_13_2_3_11_1_1287 41 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 167 (accept_3_2 40 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 68 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 167 (Polychromatic418967fa.accept_12_2_8_11_1_31
  38 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 167 (accept_3_2 37
  68 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 167
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 68 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 167 (accept_3_2 34 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 68 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 32
  68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 167 (accept_3_2 31 68
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 167
  (Polychromatic418967fa.accept_16_14_4_7_1_2380 30 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 68 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 167 (accept_3_2 28 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 68 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 167 (Polychromatic418967fa.accept_12_2_8_11_1_31
  26 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 167 (accept_3_2 25
  68 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 68 167
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 24 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 68 167 (Polychromatic418967fa.accept_13_10_3_11_1_1923 23 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 167 (accept_3_2 22 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 68 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 167 (Polychromatic418967fa.accept_13_7_3_11_1_280
  20 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 167 (accept_3_2 19
  68 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 167
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 68 167 (Polychromatic418967fa.accept_20_17_8_7_1_7859 17 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 167 (accept_3_2 16 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 68 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 167 (Polychromatic418967fa.accept_12_2_8_11_1_31
  14 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 167 (accept_3_2 13
  68 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 68 167
  (Polychromatic418967fa.accept_16_12_4_7_1_3391 12 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 68 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 167 (accept_3_2 10 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 68 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 68
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 167 (accept_3_2 7 68 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 167 (Polychromatic418967fa.accept_14_6_12_13_1_3180
  6 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 167
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 68 167 (accept_3_2 4 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68
  167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 68 167 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 167 (accept_3_2 1 68 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 167
  (allA_of_3_0 67 67 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 167 (allA_succ_of_accept 65 66 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 167 (accept_3_2 64 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 167 (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 62 66 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 167 (accept_3_2 61 66 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 66 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 167
  (Polychromatic418967fa.accept_13_7_1_11_1_732 59 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 167 (accept_3_2 58 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 66 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 167 (accept_3_2 55 66 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 167 (Polychromatic418967fa.accept_17_3_15_14_1_4219 54 66 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 167 (accept_3_2 52 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 167 (Polychromatic418967fa.accept_17_16_15_14_1_6747 50 66 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 167 (accept_3_2 49 66 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 167 (Polychromatic418967fa.accept_13_9_1_11_1_275 48 66 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 167 (accept_3_2 46 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 66 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 167 (accept_3_2 43 66 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 66 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 167 (accept_3_2 40 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 66 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 167 (accept_3_2 37 66 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 167 (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 66 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 167 (accept_3_2 34 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 66 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 167 (accept_3_2 31 66 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 66 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 167 (accept_3_2 28 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 167 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 66 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 167 (accept_3_2 25 66 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 66 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 167
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 167 (accept_3_2 22 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 66 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 167 (accept_3_2 19 66 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 66 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 167 (accept_3_2 16 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 167 (Polychromatic418967fa.accept_23_14_20_6_1_9258 14 66 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 167 (accept_3_2 13 66 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 167 (Polychromatic418967fa.accept_13_12_1_11_1_1917 12 66
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 167
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 167 (accept_3_2 10 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 66 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 167 (accept_3_2 7 66 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 66 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 66 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 167 (accept_3_2 4 66 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 167 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3
  66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 167
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 167 (accept_3_2 1 66 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 167 (allA_succ_of_accept 64 65 167
  (accept_3_2 64 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 167
  (Polychromatic418967fa.accept_10_3_5_7_1_330 63 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 167 (accept_3_2 61 65 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 65 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 59
  65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 167 (accept_3_2 58 65
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 167 (Polychromatic418967fa.accept_7_1_2_6_1_55
  57 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 167
  (Polychromatic418967fa.accept_11_1_10_2_1_58 56 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 65 167 (accept_3_2 55 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  65 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 65 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 65 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 167 (accept_3_2 52 65 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 65 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 65 167 (accept_3_2 49 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  65 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 65 167 (Polychromatic418967fa.accept_21_5_2_20_1_6081 47 65 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 167 (accept_3_2 46 65 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 65 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 65 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 65 167 (accept_3_2 43 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  65 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 65 167 (Polychromatic418967fa.accept_15_11_5_2_1_520 41 65 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 167 (accept_3_2 40 65 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 65 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 167 (accept_3_2 37 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 65 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 65 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 167 (accept_3_2 34 65 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 65 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 167
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 167 (accept_3_2 31 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 65 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 167 (accept_3_2 28 65 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 167 (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 65 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 167 (accept_3_2 25 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 167 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 65 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 167 (accept_3_2 22 65 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 65 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 167
  (Polychromatic418967fa.accept_19_1_8_15_1_3786 20 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 167 (accept_3_2 19 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 65 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 167 (accept_3_2 16 65 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 65 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 167 (accept_3_2 13 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 65 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 167 (accept_3_2 10 65 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 167 (Polychromatic418967fa.accept_20_9_5_7_1_6336 9 65 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 167
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 167 (accept_3_2 7 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 167 (Polychromatic418967fa.accept_21_5_2_20_1_6081 5 65 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 167 (accept_3_2 4 65 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 65 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 167 (accept_3_2 1 65 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  167))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 167 (allA_of_3_0 64 64 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 167 (allA_succ_of_accept 62 63 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 167 (accept_3_2 61 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 167 (Polychromatic418967fa.accept_11_5_8_2_1_588 60 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 167 (Polychromatic418967fa.accept_15_14_3_2_1_2811 59 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 167 (accept_3_2 58 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 63
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 167 (accept_3_2 55 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 167 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 167 (Polychromatic418967fa.accept_23_7_17_6_1_9257 53 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 167 (accept_3_2 52 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 167 (Polychromatic418967fa.accept_16_3_15_7_1_3417 51 63
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 167 (accept_3_2 49 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 167 (Polychromatic418967fa.accept_14_6_7_13_1_3158 48 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 167 (Polychromatic418967fa.accept_19_9_6_15_1_9256 47 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 167 (accept_3_2 46 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 167 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 63 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 167 (accept_3_2 43 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 167 (Polychromatic418967fa.accept_15_12_3_2_1_2756 42 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 167 (Polychromatic418967fa.accept_27_14_9_5_1_9255 41 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 167 (accept_3_2 40 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 167 (Polychromatic418967fa.accept_22_17_19_13_1_9253 39 63
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 167 (accept_3_2 37 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 167 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 167 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 63 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 167 (accept_3_2 34 63 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 167 (accept_3_2 31 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 167 (Polychromatic418967fa.accept_16_14_15_7_1_5655 30 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 167 (Polychromatic418967fa.accept_14_1_7_13_1_333 29 63 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 167 (accept_3_2 28 63 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 167 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 167 (accept_3_2 25 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 167 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 167 (Polychromatic418967fa.accept_19_4_6_15_1_7916 23 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 167 (accept_3_2 22 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 63
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 167 (accept_3_2 19 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 167 (Polychromatic418967fa.accept_24_18_15_23_1_9254 18 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 167 (Polychromatic418967fa.accept_22_17_19_13_1_9253 17 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 167 (accept_3_2 16 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 167 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 63 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 167 (accept_3_2 13 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 167 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 167 (Polychromatic418967fa.accept_16_11_15_7_1_5654 11 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 167 (accept_3_2 10 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 63 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 167 (accept_3_2 7 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  167 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 63 167 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 63 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 167 (accept_3_2 4 63 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 167 (Polychromatic418967fa.accept_16_3_15_7_1_3417 3 63 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 167 (accept_3_2 1 63 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  167))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 167 (allA_succ_of_accept 61 62 167
  (accept_3_2 61 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 167
  (Polychromatic418967fa.accept_9_6_8_5_1_837 60 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 167 (Polychromatic418967fa.accept_10_9_2_7_1_1096 59 62 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 167 (accept_3_2 58 62 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 56
  62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 167 (accept_3_2 55 62
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 167
  (Polychromatic418967fa.accept_10_4_2_7_1_373 54 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 167 (accept_3_2 52 62 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 62 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 167
  (Polychromatic418967fa.accept_17_16_11_14_1_4213 50 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 62 167 (accept_3_2 49 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 62 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 62 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 62 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 62 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 167 (accept_3_2 46 62 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 167
  (Polychromatic418967fa.accept_10_4_2_7_1_373 44 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 167 (accept_3_2 43 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 167 (accept_3_2 40 62 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 62 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 167 (accept_3_2 37 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 167 (Polychromatic418967fa.accept_16_4_14_7_1_5641 36 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 167 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 62 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 167 (accept_3_2 34 62 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 167
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 167 (accept_3_2 31 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 167 (accept_3_2 28 62 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 62 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 167
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 26 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 167 (accept_3_2 25 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 167 (Polychromatic418967fa.accept_19_4_5_15_1_2437 23 62 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 167 (accept_3_2 22 62 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 167 (accept_3_2 19 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 167 (Polychromatic418967fa.accept_20_18_2_7_1_6285 18 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 167 (accept_3_2 16 62 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 62 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 167
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 167 (accept_3_2 13 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 62 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 167 (accept_3_2 10 62 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 167
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 167 (accept_3_2 7 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  167 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 167 (accept_3_2 4 62 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 62 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  62 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 167 (accept_3_2 1 62 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 167 (allA_of_3_0 61 61 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 167 (allA_succ_of_accept 59 60 167
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 167 (accept_3_2 58 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 60 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 167 (accept_3_2 55 60 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 60 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 167
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 167 (accept_3_2 52 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  60 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 60 167 (Polychromatic418967fa.accept_16_2_12_7_1_3410 50 60 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 167 (accept_3_2 49 60 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 60 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 167
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 167 (accept_3_2 46 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 60 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 167 (accept_3_2 43 60 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 167 (Polychromatic418967fa.accept_13_3_8_11_1_1906 42 60 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 167
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 41 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 167 (accept_3_2 40 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 60 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 167 (accept_3_2 37 60 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 167 (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 60 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 167
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 167 (accept_3_2 34 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 167 (Polychromatic418967fa.accept_13_6_8_11_1_5398 32 60 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 167 (accept_3_2 31 60 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 60 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 167
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 167 (accept_3_2 28 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 60 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 167 (accept_3_2 25 60 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 60 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 167
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 167 (accept_3_2 22 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 60 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 167 (accept_3_2 19 60 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 167 (Polychromatic418967fa.accept_16_2_12_7_1_3410 18 60 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 167
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 167 (accept_3_2 16 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  60 167 (Polychromatic418967fa.accept_18_15_6_5_1_3972 15 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 60 167 (Polychromatic418967fa.accept_13_1_8_11_1_724 14 60 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 167 (accept_3_2 13 60 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 60 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 167
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 167 (accept_3_2 10 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 60 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 167 (accept_3_2 7 60 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 167 (Polychromatic418967fa.accept_13_6_8_11_1_5398 6 60 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 167
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 167 (accept_3_2 4 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  167 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 60 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 60 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 167 (accept_3_2 1 60 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 167
  (allA_succ_of_accept 58 59 167 (accept_3_2 58 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 167 (Polychromatic418967fa.accept_13_5_7_11_1_3470 57 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 167 (Polychromatic418967fa.accept_13_4_7_11_1_1981 56 59 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 167 (accept_3_2 55 59 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 167 (Polychromatic418967fa.accept_25_4_9_17_1_9252 54 59
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 167
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 167 (accept_3_2 52 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 167 (Polychromatic418967fa.accept_11_6_4_2_1_599 50 59 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 167 (accept_3_2 49 59 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 167 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 59 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 167
  (Polychromatic418967fa.accept_16_15_11_7_1_6951 47 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 167 (accept_3_2 46 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 167 (Polychromatic418967fa.accept_17_11_8_14_1_8084 45 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 59 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 167 (accept_3_2 43 59 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 167 (Polychromatic418967fa.accept_10_2_9_7_1_720 42 59 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 167
  (Polychromatic418967fa.accept_17_7_8_14_1_6720 41 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 167 (accept_3_2 40 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 167 (Polychromatic418967fa.accept_10_8_9_7_1_1118 38 59 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 167 (accept_3_2 37 59 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 59 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 167
  (Polychromatic418967fa.accept_13_9_7_11_1_1292 35 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 167 (accept_3_2 34 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 167 (Polychromatic418967fa.accept_15_3_14_2_1_1888 33 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 59 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 167 (accept_3_2 31 59 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 59 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 167
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 29 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 167 (accept_3_2 28 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 167 (Polychromatic418967fa.accept_13_1_7_11_1_702 27 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 167 (Polychromatic418967fa.accept_20_6_19_7_1_3375 26 59 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 167 (accept_3_2 25 59 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 167 (Polychromatic418967fa.accept_14_10_3_13_1_1530 24 59
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 167
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 167 (accept_3_2 22 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 167 (Polychromatic418967fa.accept_16_5_11_7_1_5635 21 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 59 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 167 (accept_3_2 19 59 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 59 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 167
  (Polychromatic418967fa.accept_11_6_4_2_1_599 17 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 167 (accept_3_2 16 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 167 (Polychromatic418967fa.accept_16_15_11_7_1_6951 15 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 167 (Polychromatic418967fa.accept_13_1_7_11_1_702 14 59 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 167 (accept_3_2 13 59 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 59 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 167
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 167 (accept_3_2 10 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 167 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 59 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 167 (accept_3_2 7 59 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 167 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 59 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 167 (Polychromatic418967fa.accept_13_5_7_11_1_3470
  5 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 167 (accept_3_2 4 59
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 167
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 3 59 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 59 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 167 (accept_3_2 1 59 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 167))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 167 (allA_of_3_0
  58 58 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 167 (allA_succ_of_accept 56 57 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 167 (accept_3_2 55 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 57 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 167 (accept_3_2 52 57 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 57 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 167 (accept_3_2 49 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 167 (Polychromatic418967fa.accept_15_3_12_2_1_507 48 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 57 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 167 (accept_3_2 46 57 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 167 (Polychromatic418967fa.accept_13_6_5_11_1_1971 45 57 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 167 (accept_3_2 43 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 167 (Polychromatic418967fa.accept_17_7_6_14_1_6737 41 57 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 167 (accept_3_2 40 57 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 57 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 167 (accept_3_2 37 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 167 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 57 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 167 (accept_3_2 34 57 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 57 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 167 (accept_3_2 31 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 57 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 167 (accept_3_2 28 57 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 57 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 167 (accept_3_2 25 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 57 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 167 (accept_3_2 22 57 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 167 (Polychromatic418967fa.accept_14_7_1_13_1_357 21 57 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 167 (accept_3_2 19 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 57 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 167 (accept_3_2 16 57 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 57 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 167 (accept_3_2 13 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 57 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 167 (accept_3_2 10 57 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 57 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 167 (accept_3_2 7 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 57 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 167 (accept_3_2 4 57 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 57 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 167 (accept_3_2 1 57 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 167 (allA_succ_of_accept 55 56 167 (accept_3_2 55 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 167 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 56 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 56 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 167 (accept_3_2 52 56 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 167
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 167 (accept_3_2 49 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 167 (Polychromatic418967fa.accept_11_3_1_2_1_1063 47 56 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 167 (accept_3_2 46 56 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 167 (accept_3_2 43 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 167 (Polychromatic418967fa.accept_10_1_6_7_1_710 41 56 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 167 (accept_3_2 40 56 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 167
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 167 (accept_3_2 37 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 167 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 167 (accept_3_2 34 56 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 167
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 167 (accept_3_2 31 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 167 (Polychromatic418967fa.accept_20_9_16_7_1_1129 29 56 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 167 (accept_3_2 28 56 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 167 (accept_3_2 25 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 167 (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 56 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 167 (accept_3_2 22 56 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 167
  (Polychromatic418967fa.accept_13_7_4_11_1_1967 20 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 167 (accept_3_2 19 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 167 (Polychromatic418967fa.accept_21_18_14_20_1_9251 18 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 167 (accept_3_2 16 56 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 167
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 167 (accept_3_2 13 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 167 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 56 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 167 (accept_3_2 10 56 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 167 (accept_3_2 7 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  167 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 167 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 56 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 167 (accept_3_2 4 56 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 167 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  56 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 167 (accept_3_2 1 56 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 167))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 167 (allA_of_3_0 55 55 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 167
  (allA_succ_of_accept 53 54 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 167 (accept_3_2 52 54 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 167 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 54 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 50
  54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 167 (accept_3_2 49 54
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 167
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 48 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 167 (Polychromatic418967fa.accept_16_15_6_7_1_4512 47 54 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 167 (accept_3_2 46 54 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 167
  (Polychromatic418967fa.accept_19_6_16_15_1_9250 44 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 54 167 (accept_3_2 43 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  54 167 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 54 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 167 (accept_3_2 40 54 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 54 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 54 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 167
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 38 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 167 (accept_3_2 37 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  54 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 54 167 (Polychromatic418967fa.accept_13_9_2_11_1_1964 35 54 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 167 (accept_3_2 34 54 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 54 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 167
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 54 167 (accept_3_2 31 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  54 167 (Polychromatic418967fa.accept_13_4_2_11_1_733 30 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 54 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 167 (accept_3_2 28 54 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 167 (Polychromatic418967fa.accept_19_8_16_15_1_9249 27 54 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 167
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 167 (accept_3_2 25 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  54 167 (Polychromatic418967fa.accept_21_3_12_20_1_1891 24 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 54 167 (Polychromatic418967fa.accept_10_3_4_7_1_353 23 54 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 167 (accept_3_2 22 54 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 167
  (Polychromatic418967fa.accept_14_6_12_13_1_3180 20 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 167 (accept_3_2 19 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  54 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 54 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 167 (accept_3_2 16 54 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 54 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 167
  (Polychromatic418967fa.accept_23_14_8_6_1_9248 14 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 167 (accept_3_2 13 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  54 167 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 54 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 167 (accept_3_2 10 54 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 167
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 167 (accept_3_2 7 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54
  167 (Polychromatic418967fa.accept_14_6_12_13_1_3180 6 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 54 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 167 (accept_3_2 4 54 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 54 167 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 54 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 167
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 167 (accept_3_2 1 54 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  167)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 167 (allA_succ_of_accept 52 53 167 (accept_3_2
  52 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 167
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 167 (accept_3_2 49 53 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 53 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 47
  53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 167 (accept_3_2 46 53
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 167
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 53 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 167 (accept_3_2 43 53 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 167
  (Polychromatic418967fa.accept_24_17_5_23_1_5724 41 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 167 (accept_3_2 40 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 167 (accept_3_2 37 53 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 167 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 53 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 167
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 167 (accept_3_2 34 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 167 (Polychromatic418967fa.accept_22_10_9_13_1_9247 32 53 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 167 (accept_3_2 31 53 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 167 (accept_3_2 28 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 167 (Polychromatic418967fa.accept_16_11_5_7_1_2395 27 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 167 (accept_3_2 25 53 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 53 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 167
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 167 (accept_3_2 22 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 53 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 167 (accept_3_2 19 53 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 167
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 167 (accept_3_2 16 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 167 (accept_3_2 13 53 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 53 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 167 (accept_3_2 10 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 167 (Polychromatic418967fa.accept_13_8_1_11_1_1284 8 53 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 167 (accept_3_2 7 53 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 167
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 167 (accept_3_2 4 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  167 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 53 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 167 (accept_3_2 1 53 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 167))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 167 (allA_of_3_0 52 52
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 167 (allA_succ_of_accept 50 51 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 167 (accept_3_2 49 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 51 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 167 (accept_3_2 46 51 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 51 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 167 (accept_3_2 43 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 167 (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 167 (Polychromatic418967fa.accept_15_11_6_2_1_1106 41 51 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 167 (accept_3_2 40 51 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 51 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 167 (accept_3_2 37 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 51 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 167 (accept_3_2 34 51 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 51 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 167 (accept_3_2 31 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 51 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 167 (accept_3_2 28 51 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 167 (Polychromatic418967fa.accept_13_1_12_11_1_728 27 51 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 167 (accept_3_2 25 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 167 (Polychromatic418967fa.accept_13_10_12_11_1_731 23 51 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 167 (accept_3_2 22 51 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 51 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 167 (accept_3_2 19 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 51 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 167 (accept_3_2 16 51 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 51 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 167 (accept_3_2 13 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 51 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 167 (accept_3_2 10 51 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 167 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 51 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 167 (accept_3_2 7 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  167 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 51 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 167 (Polychromatic418967fa.accept_26_5_25_11_1_9246 5 51 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 167 (accept_3_2 4 51 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 51 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 51
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 167 (accept_3_2 1 51 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 167)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 167 (allA_succ_of_accept 49 50 167 (accept_3_2 49 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 50 167 (Polychromatic418967fa.accept_11_4_6_2_1_51 48 50 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 50 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 50 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 167 (accept_3_2 46 50 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 50 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  50 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 167
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 167 (accept_3_2 43 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 167 (Polychromatic418967fa.accept_15_12_5_2_1_2786 42 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 167 (accept_3_2 40 50 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 50 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 167
  (Polychromatic418967fa.accept_20_18_10_7_1_9245 38 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 167 (accept_3_2 37 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 167 (Polychromatic418967fa.accept_17_2_16_14_1_2116 36 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 167 (Polychromatic418967fa.accept_14_7_8_13_1_3161 35 50 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 167 (accept_3_2 34 50 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 167
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 167 (accept_3_2 31 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 167 (accept_3_2 28 50 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 50 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 167
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 167 (accept_3_2 25 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 167 (Polychromatic418967fa.accept_19_5_12_15_1_9244 24 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 50 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 167 (accept_3_2 22 50 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 167
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 167 (accept_3_2 19 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 167 (Polychromatic418967fa.accept_15_3_5_2_1_2816 18 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 167 (accept_3_2 16 50 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 50 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 167
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 167 (accept_3_2 13 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 167 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 50 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 167 (accept_3_2 10 50 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 167
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 167 (accept_3_2 7 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  167 (Polychromatic418967fa.accept_19_6_12_15_1_7895 6 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 50 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 167 (accept_3_2 4 50 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 50 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 167
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 50 167 (accept_3_2 1 50 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  167)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 167 (allA_of_3_0 49 49 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 48 167 (allA_succ_of_accept 47 48 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 48
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 167 (accept_3_2 46 48 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 167 (Polychromatic418967fa.accept_10_5_8_7_1_2174
  45 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 48 167 (accept_3_2 43 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  48 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 48 167 (Polychromatic418967fa.accept_13_2_9_11_1_258 41 48 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 167 (accept_3_2 40 48 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 48 167 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 48 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 48 167 (accept_3_2 37 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  48 167 (Polychromatic418967fa.accept_19_17_10_15_1_7927 36 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 48 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 48 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 167 (accept_3_2 34 48 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 48 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 48 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 167
  (Polychromatic418967fa.accept_21_11_6_20_1_4589 32 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 48 167 (accept_3_2 31 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  48 167 (Polychromatic418967fa.accept_19_11_10_15_1_3741 30 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 48 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 48 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 167 (accept_3_2 28 48 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 48 167 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 48 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 48 167 (accept_3_2 25 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  48 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 48 167 (Polychromatic418967fa.accept_19_4_10_15_1_9243 23 48 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 167 (accept_3_2 22 48 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 48 167 (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 48
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 48 167 (accept_3_2 19 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  48 167 (Polychromatic418967fa.accept_21_18_6_20_1_9242 18 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 48 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 48 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 167 (accept_3_2 16 48 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 48 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 48 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 167
  (Polychromatic418967fa.accept_13_1_9_11_1_703 14 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 48 167 (accept_3_2 13 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  48 167 (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 48 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 48 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 167 (accept_3_2 10 48 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 48 167 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 48 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 48 167 (accept_3_2 7 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48
  167 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 48 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 167 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 48 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 167 (accept_3_2 4 48 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 48 167 (Polychromatic418967fa.accept_19_3_10_15_1_9241 3 48 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 48
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 167 (accept_3_2 1 48 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 167)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 167 (allA_succ_of_accept 46 47 167 (accept_3_2 46 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 47 167 (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 47 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 47 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 167 (accept_3_2 43 47 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 42
  47 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 167
  (Polychromatic418967fa.accept_19_3_9_15_1_9240 41 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 167 (accept_3_2 40 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 167 (Polychromatic418967fa.accept_16_6_15_7_1_1510 38 47 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 167 (accept_3_2 37 47 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 47 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 167 (accept_3_2 34 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 47 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 167 (accept_3_2 31 47 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 47 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 167
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 167 (accept_3_2 28 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 167 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 47 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 167 (accept_3_2 25 47 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 47 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 167
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 167 (accept_3_2 22 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 167 (Polychromatic418967fa.accept_14_6_5_13_1_367 20 47 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 167 (accept_3_2 19 47 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 47 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 167 (accept_3_2 16 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 167 (Polychromatic418967fa.accept_13_1_8_11_1_724 14 47 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 167 (accept_3_2 13 47 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 47 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 167
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 167 (accept_3_2 10 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 167 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 47 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 167 (accept_3_2 7 47 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 47 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 167
  (Polychromatic418967fa.accept_19_5_9_15_1_9239 5 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 167 (accept_3_2 4 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  167 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 47 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 167 (Polychromatic418967fa.accept_19_2_9_15_1_9238 2 47 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 167 (accept_3_2 1 47 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 167))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 167 (allA_of_3_0 46 46 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 167 (allA_succ_of_accept 44 45 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 167 (accept_3_2 43 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 167 (Polychromatic418967fa.accept_16_9_13_7_1_1509 41 45 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 167 (accept_3_2 40 45 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 45 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 167 (accept_3_2 37 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 167 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 167 (Polychromatic418967fa.accept_20_15_5_7_1_4791 35 45 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 167 (accept_3_2 34 45 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 167 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 45 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 167 (accept_3_2 31 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 167 (Polychromatic418967fa.accept_17_12_11_14_1_3120 29 45 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 167 (accept_3_2 28 45 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 45 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 167 (accept_3_2 25 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 167 (Polychromatic418967fa.accept_14_10_3_13_1_1530 24 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 45 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 167 (accept_3_2 22 45 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 167 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 45 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 167 (accept_3_2 19 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 167 (Polychromatic418967fa.accept_13_4_6_11_1_2017 17 45 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 167 (accept_3_2 16 45 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 45 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 167 (accept_3_2 13 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 167 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 45 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 167 (accept_3_2 10 45 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 45 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 167 (accept_3_2 7 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 167 (Polychromatic418967fa.accept_13_5_6_11_1_1933 5 45 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 167 (accept_3_2 4 45 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 167 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 45 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 167 (accept_3_2 1 45 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 167))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  167 (allA_succ_of_accept 43 44 167 (accept_3_2 43 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 44 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 167 (Polychromatic418967fa.accept_10_1_4_7_1_374 41 44 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 167 (accept_3_2 40 44 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 167
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 167 (accept_3_2 37 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 44 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 167 (accept_3_2 34 44 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 167
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 167 (accept_3_2 31 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 44 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 167 (accept_3_2 28 44 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 167
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 167 (accept_3_2 25 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 167 (Polychromatic418967fa.accept_10_3_4_7_1_353 23 44 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 167 (accept_3_2 22 44 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 167 (accept_3_2 19 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 44 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 167 (accept_3_2 16 44 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 167
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 167 (accept_3_2 13 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 44 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 167 (accept_3_2 10 44 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 167
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 167 (accept_3_2 7 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  167 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 44 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 167 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 44 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 167 (accept_3_2 4 44 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  44 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 167 (accept_3_2 1 44 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 167)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  167 (allA_of_3_0 43 43 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 167 (allA_succ_of_accept 41 42 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 167 (accept_3_2 40 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 42 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 167 (accept_3_2 37 42 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 167 (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 42 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 167
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 167 (accept_3_2 34 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 167 (Polychromatic418967fa.accept_19_13_4_15_1_7902 32 42 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 167 (accept_3_2 31 42 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 42 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 167 (accept_3_2 28 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 167 (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 42 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 167 (accept_3_2 25 42 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 167 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 42 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 167
  (Polychromatic418967fa.accept_13_10_3_11_1_1923 23 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 167 (accept_3_2 22 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 42 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 167 (accept_3_2 19 42 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 167 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 42 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 167 (accept_3_2 16 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 167 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 167 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 42 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 167 (accept_3_2 13 42 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 42 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 167
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 167 (accept_3_2 10 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 42 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 42 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 167 (accept_3_2 7 42 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 42 167 (Polychromatic418967fa.accept_15_6_12_2_1_2803 6 42 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 167 (accept_3_2 4 42 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 42
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 167
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 167 (accept_3_2 1 42 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  167)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 167 (allA_succ_of_accept 40 41 167 (accept_3_2 40 41 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 167 (Polychromatic418967fa.accept_15_9_11_2_1_1882
  39 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 167 (accept_3_2 37 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 167 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 167 (Polychromatic418967fa.accept_13_9_2_11_1_1964 35 41 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 167 (accept_3_2 34 41 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 167 (Polychromatic418967fa.accept_22_11_19_13_1_9237 33 41
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 167
  (Polychromatic418967fa.accept_22_10_19_13_1_9236 32 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 41 167 (accept_3_2 31 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 41 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 167 (Polychromatic418967fa.accept_13_3_2_11_1_1999 29 41
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 167 (accept_3_2 28 41 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 167 (Polychromatic418967fa.accept_11_5_8_2_1_588
  27 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 167 (accept_3_2 25 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 167 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 167 (Polychromatic418967fa.accept_13_10_2_11_1_1920 23 41 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 167 (accept_3_2 22 41 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 167 (Polychromatic418967fa.accept_15_6_11_2_1_2801 21 41
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 167
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 167 (accept_3_2 19 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 167 (Polychromatic418967fa.accept_13_4_2_11_1_733 17 41 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 167 (accept_3_2 16 41 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 167 (Polychromatic418967fa.accept_20_15_1_7_1_9235 15 41 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 167 (accept_3_2 13 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 167 (Polychromatic418967fa.accept_19_12_3_15_1_9234 12 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 167 (Polychromatic418967fa.accept_20_11_1_7_1_9233 11 41 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 167 (accept_3_2 10 41 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 167 (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 41 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 167
  (Polychromatic418967fa.accept_16_8_9_7_1_768 8 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 167 (accept_3_2 7 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 167 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 41 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 167 (accept_3_2 4 41 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 167 (Polychromatic418967fa.accept_13_3_2_11_1_1999 3 41 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 167 (accept_3_2 1 41 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 167))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 167
  (allA_of_3_0 40 40 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 167 (allA_succ_of_accept 38 39 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 167 (accept_3_2 37 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 167 (Polychromatic418967fa.accept_17_2_5_14_1_2068 36 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 167 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 39 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 167 (accept_3_2 34 39 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 39 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 167 (accept_3_2 31 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 39 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 167 (accept_3_2 28 39 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 167 (Polychromatic418967fa.accept_17_10_5_14_1_4203 27 39 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 167 (accept_3_2 25 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 39 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 167 (accept_3_2 22 39 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 39 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 167 (accept_3_2 19 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 167 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 39 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 167 (accept_3_2 16 39 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 39 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 167 (accept_3_2 13 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 39 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 167 (accept_3_2 10 39 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 39 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 167 (accept_3_2 7 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  167 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 39 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 39 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 167 (accept_3_2 4 39 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 39 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 39
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 167 (accept_3_2 1 39 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 167))))))))))))))))))))))))))))))))))))))) (allB_succ 38 167
  (allA_succ_of_accept 37 38 167 (accept_3_2 37 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 167 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 38 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 167 (accept_3_2 34 38 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 167
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 167 (accept_3_2 31 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 167 (accept_3_2 28 38 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 38 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 167 (accept_3_2 25 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 38 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 167 (accept_3_2 22 38 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 167
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 167 (accept_3_2 19 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 167 (accept_3_2 16 38 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 38 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 167
  (Polychromatic418967fa.accept_13_1_12_11_1_728 14 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 167 (accept_3_2 13 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 38 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 167 (accept_3_2 10 38 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 167 (accept_3_2 7 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  167 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 38 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 167 (accept_3_2 4 38 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 38 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 38
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 167 (accept_3_2 1 38 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 167)))))))))))))))))))))))))))))))))))))) (allB_succ 37 167
  (allA_of_3_0 37 37 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 167 (allA_succ_of_accept 35 36 167
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 167 (accept_3_2 34 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 167 (Polychromatic418967fa.accept_19_13_17_15_1_7928 32 36 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 167 (accept_3_2 31 36 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 36 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 167
  (Polychromatic418967fa.accept_13_3_10_11_1_1293 29 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 167 (accept_3_2 28 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 36 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 167 (accept_3_2 25 36 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 167 (Polychromatic418967fa.accept_16_8_4_7_1_3390 24 36 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 167
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 167 (accept_3_2 22 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 167 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 167 (Polychromatic418967fa.accept_17_3_2_14_1_6714 20 36 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 167 (accept_3_2 19 36 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 167 (Polychromatic418967fa.accept_21_18_15_20_1_6076 18 36
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 167
  (Polychromatic418967fa.accept_13_4_10_11_1_1908 17 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 167 (accept_3_2 16 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 167 (Polychromatic418967fa.accept_13_2_10_11_1_1276 15 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 167 (Polychromatic418967fa.accept_13_1_10_11_1_1280 14 36 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 167 (accept_3_2 13 36 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 36 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 167
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 167 (accept_3_2 10 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 167 (Polychromatic418967fa.accept_13_8_10_11_1_2730 8 36 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 167 (accept_3_2 7 36 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 167 (Polychromatic418967fa.accept_20_6_16_7_1_9232 6 36 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 167
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 167 (accept_3_2 4 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  167 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 36 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 36 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 167 (accept_3_2 1 36 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 167)))))))))))))))))))))))))))))))))))) (allB_succ 35 167 (allA_succ_of_accept 34 35 167
  (accept_3_2 34 35 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 167
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 35 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 167 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 35 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 167 (accept_3_2 31 35 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 35 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 29
  35 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 167 (accept_3_2 28 35
  167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 167
  (Polychromatic418967fa.accept_13_1_9_11_1_703 27 35 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 167 (Polychromatic418967fa.accept_15_11_5_2_1_520 26 35 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 167 (accept_3_2 25 35 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 167 (Polychromatic418967fa.accept_10_3_5_7_1_330
  23 35 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 167 (accept_3_2 22
  35 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 167
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 35 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 35 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 35 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 167 (accept_3_2 19 35 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 35 167 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 35 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 167
  (Polychromatic418967fa.accept_21_17_14_20_1_7811 17 35 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 35 167 (accept_3_2 16 35 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 35 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 35 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 167 (Polychromatic418967fa.accept_13_1_9_11_1_703 14 35 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 167 (accept_3_2 13 35 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 12
  35 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 35 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 167 (accept_3_2 10 35 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 167 (Polychromatic418967fa.accept_16_9_3_7_1_6883 9 35 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 35 167 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 35 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 167 (accept_3_2 7 35 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 35 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 167
  (Polychromatic418967fa.accept_20_5_15_7_1_7869 5 35 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 167 (accept_3_2 4 35 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  167 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 35 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 35 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 167 (accept_3_2 1 35 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 167))))))))))))))))))))))))))))))))))) (allB_succ 34 167 (allA_of_3_0 34 34 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 33 167 (allA_succ_of_accept 32 33 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 167 (accept_3_2 31 33 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 33 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 167 (accept_3_2 28 33 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 167 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 33 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 167 (accept_3_2 25 33 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 167 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 33 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 167 (Polychromatic418967fa.accept_19_4_14_15_1_9231 23 33 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 167 (accept_3_2 22 33 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 33 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 167 (accept_3_2 19 33 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 33 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 167 (accept_3_2 16 33 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 33 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 167 (accept_3_2 13 33 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 33 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 33 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 167 (accept_3_2 10 33 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 167 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 33 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 167 (accept_3_2 7 33 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 167 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 33 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 167 (accept_3_2 4 33 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 33 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 167 (accept_3_2 1 33 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 167))))))))))))))))))))))))))))))))) (allB_succ 32 167
  (allA_succ_of_accept 31 32 167 (accept_3_2 31 32 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  32 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 32 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 32 167 (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 32 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 167 (accept_3_2 28 32 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 167
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 32 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 167 (accept_3_2 25 32 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 32 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 167 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 32 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 167 (accept_3_2 22 32 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 167
  (Polychromatic418967fa.accept_17_3_15_14_1_4219 20 32 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 167 (accept_3_2 19 32 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 167 (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 32 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 32 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 167 (accept_3_2 16 32 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 167
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 32 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 167 (accept_3_2 13 32 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 32 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 167 (Polychromatic418967fa.accept_18_11_14_5_1_3951 11 32 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 167 (accept_3_2 10 32 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 167
  (Polychromatic418967fa.accept_13_8_6_11_1_1979 8 32 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 167 (accept_3_2 7 32 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  167 (Polychromatic418967fa.accept_17_6_15_14_1_8027 6 32 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 32 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 32 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 167 (accept_3_2 4 32 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 32 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 167
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 32 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 32 167 (accept_3_2 1 32 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32
  167)))))))))))))))))))))))))))))))) (allB_succ 31 167 (allA_of_3_0 31 31 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 30 167 (allA_succ_of_accept 29 30 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 167 (accept_3_2 28 30 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 30 167 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 30 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 30 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 30 167 (accept_3_2 25 30 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  30 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 30 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 30 167 (Polychromatic418967fa.accept_13_10_4_11_1_1969 23 30 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 167 (accept_3_2 22 30 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 30 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 30 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 30 167 (accept_3_2 19 30 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  30 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 30 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 30 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 167 (accept_3_2 16 30 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 30 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 30 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 167
  (Polychromatic418967fa.accept_19_14_11_15_1_9230 14 30 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 30 167 (accept_3_2 13 30 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 30 167 (Polychromatic418967fa.accept_13_12_4_11_1_1925 12 30 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 30 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 167 (accept_3_2 10 30 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 30 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 167
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 30 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 167 (accept_3_2 7 30 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30
  167 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 30 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 30 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 167 (accept_3_2 4 30 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 30 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 30 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 30
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 167 (accept_3_2 1 30 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 167)))))))))))))))))))))))))))))) (allB_succ 29 167
  (allA_succ_of_accept 28 29 167 (accept_3_2 28 29 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  29 167 (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 29 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 167 (accept_3_2 25 29 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 29 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 167
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 29 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 167 (accept_3_2 22 29 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 167 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 29 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 167 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 29 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 167 (accept_3_2 19 29 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 167
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 29 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 167 (accept_3_2 16 29 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 29 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 167 (accept_3_2 13 29 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 29 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 167
  (Polychromatic418967fa.accept_17_11_12_14_1_5431 11 29 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 29 167 (accept_3_2 10 29 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 29 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 29 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 167 (accept_3_2 7 29 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 167
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 29 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 167 (accept_3_2 4 29 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  167 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 29 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 167 (accept_3_2 1 29 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 167))))))))))))))))))))))))))))) (allB_succ 28 167 (allA_of_3_0 28 28 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 167 (allA_succ_of_accept 26 27 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 27
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 167 (accept_3_2 25 27 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 167
  (Polychromatic418967fa.accept_17_7_10_14_1_8022 24 27 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 167 (Polychromatic418967fa.accept_13_10_1_11_1_1961 23 27 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 167 (accept_3_2 22 27 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 27 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 167 (accept_3_2 19 27 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 167 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 27 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 167 (Polychromatic418967fa.accept_19_17_8_15_1_6448 17 27 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 167 (accept_3_2 16 27 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 167 (Polychromatic418967fa.accept_16_15_11_7_1_6951 15 27
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 27 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 167 (accept_3_2 13 27 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 167 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 27 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 167 (Polychromatic418967fa.accept_21_11_6_20_1_4589 11 27 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 167 (accept_3_2 10 27 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 167 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 27 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 167 (accept_3_2 7 27 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  167 (Polychromatic418967fa.accept_15_6_12_2_1_2803 6 27 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 27 167 (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 27 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 167 (accept_3_2 4 27 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 167 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 27 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 27 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 167 (accept_3_2 1 27 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27
  167))))))))))))))))))))))))))) (allB_succ 26 167 (allA_succ_of_accept 25 26 167 (accept_3_2 25 26 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 26 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 26 167
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 26 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 26 167 (accept_3_2 22 26 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  26 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 26 167 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 26 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 167 (accept_3_2 19 26 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 26 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 26 167 (accept_3_2 16 26 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  26 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 26 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 26 167 (Polychromatic418967fa.accept_16_14_10_7_1_2363 14 26 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 167 (accept_3_2 13 26 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 26 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 167
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 26 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 167 (accept_3_2 10 26 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  26 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 26 167 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 26 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 167 (accept_3_2 7 26 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 26 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 26 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 167 (accept_3_2 4 26 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 26
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 167
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 26 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 167 (accept_3_2 1 26 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  167)))))))))))))))))))))))))) (allB_succ 25 167 (allA_of_3_0 25 25 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 167 (allA_succ_of_accept 23 24 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 24 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 167 (accept_3_2 22 24 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 24 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 167
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 24 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 167 (accept_3_2 19 24 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  24 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 24 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 24 167 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 167 (accept_3_2 16 24 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 167 (Polychromatic418967fa.accept_16_15_8_7_1_3407 15 24 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 167
  (Polychromatic418967fa.accept_28_14_24_27_1_9229 14 24 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 24 167 (accept_3_2 13 24 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 24 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 24 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 24 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 167 (accept_3_2 10 24 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 24
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 167
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 24 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 24 167 (accept_3_2 7 24 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24
  167 (Polychromatic418967fa.accept_17_6_7_14_1_6704 6 24 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 24 167 (Polychromatic418967fa.accept_22_5_2_13_1_9228 5 24 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 167 (accept_3_2 4 24 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 167
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 24 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 167 (accept_3_2 1 24 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24
  167)))))))))))))))))))))))) (allB_succ 23 167 (allA_succ_of_accept 22 23 167 (accept_3_2 22 23 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 167 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 23 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 167
  (Polychromatic418967fa.accept_17_3_6_14_1_4312 20 23 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 167 (accept_3_2 19 23 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 23 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 23 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 167 (accept_3_2 16 23 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 167 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 23 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 167
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 23 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 167 (accept_3_2 13 23 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 167 (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 23 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 167 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 23 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 167 (accept_3_2 10 23 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 167 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 23 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 167
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 23 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 167 (accept_3_2 7 23 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  167 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 23 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 23 167 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 23 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 167 (accept_3_2 4 23 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 23 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 167
  (Polychromatic418967fa.accept_13_2_10_11_1_1276 2 23 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 167 (accept_3_2 1 23 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  167))))))))))))))))))))))) (allB_succ 22 167 (allA_of_3_0 22 22 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 21 167 (allA_succ_of_accept 20 21 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 167 (accept_3_2 19 21 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 167
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 21 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 167 (accept_3_2 16 21 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 167 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 21 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 167 (accept_3_2 13 21 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 167 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 21 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 167
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 21 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 167 (accept_3_2 10 21 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 167 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 21 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 167 (accept_3_2 7 21 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 167
  (Polychromatic418967fa.accept_24_5_21_23_1_9227 5 21 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 167 (accept_3_2 4 21 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  167 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 21 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 21 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 167 (accept_3_2 1 21 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 21 167))))))))))))))))))))) (allB_succ 20 167 (allA_succ_of_accept 19 20 167
  (accept_3_2 19 20 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 167
  (Polychromatic418967fa.accept_11_7_9_2_1_260 18 20 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 20 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 167 (accept_3_2 16 20 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 167 (Polychromatic418967fa.accept_12_2_8_11_1_31
  14 20 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 167 (accept_3_2 13
  20 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 167
  (Polychromatic418967fa.accept_9_3_2_5_1_234 12 20 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 20 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 167 (accept_3_2 10 20 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 8
  20 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 167 (accept_3_2 7 20 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  20 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 167
  (Polychromatic418967fa.accept_13_5_7_11_1_3470 5 20 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 167 (accept_3_2 4 20 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 167 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 20 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 167 (accept_3_2 1 20 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 167)))))))))))))))))))) (allB_succ 19 167 (allA_of_3_0 19 19 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 167 (allA_succ_of_accept 17 18 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 167 (accept_3_2 16 18 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 167 (Polychromatic418967fa.accept_10_5_8_7_1_2174
  15 18 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 167
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 18 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 167 (accept_3_2 13 18 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 18 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 167 (Polychromatic418967fa.accept_16_11_2_7_1_3374 11 18 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 167 (accept_3_2 10 18 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 167
  (Polychromatic418967fa.accept_24_8_18_23_1_9226 8 18 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 167 (accept_3_2 7 18 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  167 (Polychromatic418967fa.accept_13_6_5_11_1_1971 6 18 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 18 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 167 (accept_3_2 4 18 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 18 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 167
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 18 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 18 167 (accept_3_2 1 18 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  167)))))))))))))))))) (allB_succ 17 167 (allA_succ_of_accept 16 17 167 (accept_3_2 16 17 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 17 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 167 (accept_3_2 13 17 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 17 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 167 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 17 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 167 (accept_3_2 10 17 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 167 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 17 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 167
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 8 17 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 167 (accept_3_2 7 17 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 167 (Polychromatic418967fa.accept_19_5_17_15_1_9225 5 17 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 167 (accept_3_2 4 17 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 167 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 17 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 167 (accept_3_2 1 17 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 167))))))))))))))))) (allB_succ 16 167 (allA_of_3_0 16 16 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 167 (allA_succ_of_accept 14 15 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 15 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 167 (accept_3_2 13 15 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 15 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 15 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 167 (accept_3_2 10 15 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 167 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 15 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 167
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 167 (accept_3_2 7 15 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  167 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 15 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 15 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 167 (accept_3_2 4 15 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 167 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 15 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 15
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 167 (accept_3_2 1 15 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 167))))))))))))))) (allB_succ 14 167 (allA_succ_of_accept 13 14
  167 (accept_3_2 13 14 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 167
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 14 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 167 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 14 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 167 (accept_3_2 10 14 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 167 (Polychromatic418967fa.accept_12_8_2_11_1_246 8
  14 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 167 (accept_3_2 7 14 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 167 (Polychromatic418967fa.accept_21_6_14_20_1_4594
  6 14 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 167
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 167 (accept_3_2 4 14 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 14 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 167 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 14 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 167 (accept_3_2 1 14 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 167)))))))))))))) (allB_succ 13 167 (allA_of_3_0 13 13 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 167 (allA_succ_of_accept 11 12 167 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 12 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 167 (accept_3_2 10 12 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 167 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9
  12 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 167
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 12 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 167 (accept_3_2 7 12 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12
  167 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 12 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 167 (Polychromatic418967fa.accept_10_5_2_7_1_345 5 12 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 167 (accept_3_2 4 12 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 12 167 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 12 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 167 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 12
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 167 (accept_3_2 1 12 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 167)))))))))))) (allB_succ 11 167 (allA_succ_of_accept 10 11 167
  (accept_3_2 10 11 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 167
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 11 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 167 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 11 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 167 (accept_3_2 7 11 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 167 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 11 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 167 (Polychromatic418967fa.accept_7_5_4_6_1_167 5
  11 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 167 (accept_3_2 4 11 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 167 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  11 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 167
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 11 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 167 (accept_3_2 1 11 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  167))))))))))) (allB_succ 10 167 (allA_of_3_0 10 10 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 167
  (allA_succ_of_accept 8 9 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 167 (accept_3_2 7 9 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 167 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 167 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 167 (Polychromatic418967fa.accept_17_5_9_14_1_4282 5
  9 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 167 (accept_3_2 4 9 167
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 167 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 9
  167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 167 (accept_3_2 1 9 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 167)))))))))
  (allB_succ 8 167 (allA_succ_of_accept 7 8 167 (accept_3_2 7 8 167 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 8 167 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 8 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 167 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 8 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 167 (accept_3_2 4 8 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 167 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 167
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 8 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 8 167 (accept_3_2 1 8 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 167))))))))
  (allB_succ 7 167 (allA_of_3_0 7 7 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 167 (allA_succ_of_accept 5
  6 167 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 167 (accept_3_2 4 6 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 167
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 6 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 167 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 6 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 167 (accept_3_2 1 6 167 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 167)))))) (allB_succ 5 167 (allA_succ_of_accept 4 5 167 (accept_3_2 4 5 167 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 167 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 5 167
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 167
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 167 (accept_3_2 1 5 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 167)))))
  (allB_succ 4 167 (allA_of_3_0 4 4 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 167 (allA_succ_of_accept 2
  3 167 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 3 167 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 167 (accept_3_2 1 3 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 167)))
  (allB_succ 2 167 (allA_succ_of_accept 1 2 167 (accept_3_2 1 2 167 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  167)) (allB_two
  167)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


