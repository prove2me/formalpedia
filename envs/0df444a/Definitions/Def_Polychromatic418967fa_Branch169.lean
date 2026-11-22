-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch169
-- name    : Polychromatic418967fa_Branch169
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:18:49.165317+00:00
-- url     : https://prove2.me/theorems/6cb6f999-43cf-404c-b699-6432b6251cd8
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

def Polychromatic418967fa.branch_169 : allB 169 169 :=
  allB_succ' 2 168 169 (Eq.refl Bool.true) (allA_succ_of_accept 1 168 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  168 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168 169)) (allB_succ' 3 167 169
  (Eq.refl Bool.true) (allA_of_3_1 3 167 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 166 169 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 166 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 166 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 166 169 (accept_3_3 2 166 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 166 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 166 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 169)))) (allB_succ' 5 165 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 165 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 165 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 165 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 169 (accept_3_3 2 165 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1
  165 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165 169))))) (allB_succ' 6 164 169
  (Eq.refl Bool.true) (allA_of_3_1 6 164 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 163 169 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 163 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 163 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 169 (accept_3_3 5 163 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 163 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 163 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 169 (accept_3_3 2 163 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 169 (Polychromatic418967fa.accept_22_1_9_15_1_9529 1 163 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 169))))))) (allB_succ' 8 162 169 (Eq.refl Bool.true) (allA_succ_of_accept 7 162 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 162 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 162 169 (Polychromatic418967fa.accept_16_6_2_9_1_5897 6 162 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 162 169 (accept_3_3 5 162 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 162 169 (Polychromatic418967fa.accept_19_4_10_17_1_5194 4 162 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 162 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 162 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 162 169 (accept_3_3 2 162 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  162 169 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 162 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 162 169)))))))) (allB_succ' 9 161 169 (Eq.refl Bool.true) (allA_of_3_1 9 161 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 160 169 (Eq.refl Bool.true) (allA_succ_of_accept 9 160 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 160 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 160 169 (accept_3_3 8 160 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  160 169 (Polychromatic418967fa.accept_14_7_6_1_1_1656 7 160 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 160 169 (Polychromatic418967fa.accept_15_6_10_4_1_150 6 160 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 160 169 (accept_3_3 5 160 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 160 169 (Polychromatic418967fa.accept_18_4_16_7_1_1873 4 160 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 160 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 160 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 160 169 (accept_3_3 2 160 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  160 169 (Polychromatic418967fa.accept_18_1_16_7_1_2897 1 160 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 160 169)))))))))) (allB_succ' 11 159 169 (Eq.refl Bool.true) (allA_succ_of_accept 10 159 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 159 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 159 169 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 159 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 169 (accept_3_3 8 159 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 159 169 (Polychromatic418967fa.accept_17_7_6_16_1_2195 7 159 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 159 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 159 169 (accept_3_3 5 159 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  159 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 159 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 159 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 159 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 169 (accept_3_3 2 159 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 159 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159 169))))))))))) (allB_succ' 12 158 169 (Eq.refl
  Bool.true) (allA_of_3_1 12 158 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 157 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 12 157 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 157 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 169 (accept_3_3 11 157 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 157 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 157 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 9
  157 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 169 (accept_3_3 8 157
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 169
  (Polychromatic418967fa.accept_11_7_3_4_1_729 7 157 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 157 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 157 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 169 (accept_3_3 5 157 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 157 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 157 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 3
  157 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 169 (accept_3_3 2 157
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 169 (Polychromatic418967fa.accept_9_1_4_7_1_7
  1 157 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157 169))))))))))))) (allB_succ' 14
  156 169 (Eq.refl Bool.true) (allA_succ_of_gcd 13 156 169 13 1 12 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 156 169 (Polychromatic418967fa.accept_21_12_9_1_1_9528 12 156
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 156 169 (accept_3_3 11 156
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 10 156 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 156 169 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 156 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 156 169 (accept_3_3 8 156 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 156 169 (Polychromatic418967fa.accept_17_7_3_16_1_2208 7 156 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 169
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 156 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 156 169 (accept_3_3 5 156 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  156 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 156 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 156 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 156 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 169 (accept_3_3 2 156 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 156 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 169)))))))))))))) (allB_succ' 15 155 169 (Eq.refl
  Bool.true) (allA_of_3_1 15 155 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 154 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 154 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 154 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 154 169 (accept_3_3 14 154 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 154 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 154 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 154 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 12
  154 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 154 169 (accept_3_3 11
  154 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 154 169
  (Polychromatic418967fa.accept_19_10_2_17_1_675 10 154 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 154 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 154 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 154 169 (accept_3_3 8 154 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 154 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 154 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 154 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 6
  154 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 154 169 (accept_3_3 5 154
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 154 169
  (Polychromatic418967fa.accept_9_4_1_7_1_293 4 154 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 154 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 154 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 154 169 (accept_3_3 2 154 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 154 169 (Polychromatic418967fa.accept_16_1_10_9_1_4645 1 154 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154 169)))))))))))))))) (allB_succ' 17 153 169 (Eq.refl
  Bool.true) (allA_succ_of_accept 16 153 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 153 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 169 (Polychromatic418967fa.accept_12_3_9_1_1_290
  15 153 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 169 (accept_3_3 14
  153 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 169
  (Polychromatic418967fa.accept_23_13_15_8_1_9527 13 153 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 153 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 153 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 169 (accept_3_3 11 153 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 153 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 169
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 153 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 153 169 (accept_3_3 8 153 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  153 169 (Polychromatic418967fa.accept_14_7_13_1_1_922 7 153 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 153 169 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 153 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 169 (accept_3_3 5 153 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 153 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 169
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 153 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 169 (accept_3_3 2 153 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 169 (Polychromatic418967fa.accept_15_1_3_4_1_1217 1 153 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153 169))))))))))))))))) (allB_succ' 18 152 169 (Eq.refl Bool.true) (allA_of_3_1 18 152 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 151 169 (Eq.refl Bool.true) (allA_succ_of_accept 18 151 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 151 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 169 (accept_3_3 17 151 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 169 (Polychromatic418967fa.accept_19_16_18_17_1_6570 16 151 169 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 169 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 151 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 169 (accept_3_3 14 151 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 169 (Polychromatic418967fa.accept_16_13_7_9_1_2606 13 151
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 169
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 151 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 169 (accept_3_3 11 151 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 151 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 169 (Polychromatic418967fa.accept_27_9_16_7_1_9526 9 151 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 169 (accept_3_3 8 151 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 169 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 151 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 151 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 169 (accept_3_3 5 151 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 169 (Polychromatic418967fa.accept_14_4_11_1_1_940 4 151 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 151 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 169 (accept_3_3 2 151 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 169 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 151 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 169))))))))))))))))))) (allB_succ' 20 150 169
  (Eq.refl Bool.true) (allA_succ_of_accept 19 150 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 150 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 169
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 150 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 150 169 (accept_3_3 17 150 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 150 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 150 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 150 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 150 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 169 (accept_3_3 14 150 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 150 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 169
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 150 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 150 169 (accept_3_3 11 150 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 150 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 150 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 150 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 150 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 169 (accept_3_3 8 150 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 150 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 169
  (Polychromatic418967fa.accept_20_6_10_9_1_3486 6 150 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 150 169 (accept_3_3 5 150 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  150 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 150 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 150 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 150 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 169 (accept_3_3 2 150 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 150 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 169)))))))))))))))))))) (allB_succ' 21 149 169
  (Eq.refl Bool.true) (allA_of_3_1 21 149 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 148 169 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 148 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 148 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 148 169 (accept_3_3 20 148 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 148 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 148 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 148 169
  (Polychromatic418967fa.accept_17_1_12_16_1_2211 18 148 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 148 169 (accept_3_3 17 148 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 148 169 (Polychromatic418967fa.accept_14_2_8_1_1_1647 16 148 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 148 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 148 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 148 169 (accept_3_3 14 148 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 148 169 (Polychromatic418967fa.accept_8_5_4_1_1_111
  13 148 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 148 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 148 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 148 169 (accept_3_3 11 148 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 148 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 148 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 148 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 148 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 169 (accept_3_3 8 148 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 148 169 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 148 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 148 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 148 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 148 169 (accept_3_3 5 148 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  148 169 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 148 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 148 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 148 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 169 (accept_3_3 2 148 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 148 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 148 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 169)))))))))))))))))))))) (allB_succ' 23 147 169
  (Eq.refl Bool.true) (allA_succ_of_accept 22 147 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 147 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 169
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 147 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 147 169 (accept_3_3 20 147 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 147 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 147 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 147 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 147 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 169 (accept_3_3 17 147 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 147 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 147 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 147 169 (accept_3_3 14 147 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 147 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 147 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 147 169 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 147 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 169 (accept_3_3 11 147 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 147 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 169
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 147 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 147 169 (accept_3_3 8 147 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  147 169 (Polychromatic418967fa.accept_15_7_12_4_1_1236 7 147 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 147 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 147 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 169 (accept_3_3 5 147 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 147 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 169
  (Polychromatic418967fa.accept_19_3_14_17_1_6603 3 147 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 147 169 (accept_3_3 2 147 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  147 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 147 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 147 169))))))))))))))))))))))) (allB_succ' 24 146 169 (Eq.refl Bool.true) (allA_of_3_1 24 146
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 145 169 (Eq.refl Bool.true) (allA_succ_of_accept 24 145
  169 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 145 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 145 169 (accept_3_3 23 145 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 145 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 145 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 145 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 145 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 169 (accept_3_3 20 145 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 169 (Polychromatic418967fa.accept_23_19_7_8_1_9525 19 145 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 169
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 145 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 169 (accept_3_3 17 145 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 169 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 145 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 145 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 145 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 169 (accept_3_3 14 145 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 145 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 169
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 145 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 169 (accept_3_3 11 145 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 145 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 169 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 145 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 169 (accept_3_3 8 145 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 169 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 145 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 169
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 145 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 169 (accept_3_3 5 145 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 145 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 145 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 169 (accept_3_3 2 145 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 169 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 145 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145 169))))))))))))))))))))))))) (allB_succ' 26 144 169
  (Eq.refl Bool.true) (allA_succ_of_accept 25 144 169 (Polychromatic418967fa.accept_10_5_4_9_1_420 25 144 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 144 169
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 144 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 144 169 (accept_3_3 23 144 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 144 169 (Polychromatic418967fa.accept_20_2_4_9_1_9524 22 144 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 144 169 (Polychromatic418967fa.accept_15_6_9_4_1_1227 21 144 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 169 (accept_3_3 20 144 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 144 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 144 169
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 144 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 144 169 (accept_3_3 17 144 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 144 169 (Polychromatic418967fa.accept_23_16_6_8_1_9523 16 144 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 144 169 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 144 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 144 169 (accept_3_3 14 144 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 144 169 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 144 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 144 169
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 144 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 144 169 (accept_3_3 11 144 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 144 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 144 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 144 169 (Polychromatic418967fa.accept_17_9_8_16_1_2176 9 144 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 144 169 (accept_3_3 8 144 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 169 (Polychromatic418967fa.accept_17_7_8_16_1_6966 7 144
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 144 169
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 6 144 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 144 169 (accept_3_3 5 144 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  144 169 (Polychromatic418967fa.accept_19_4_11_17_1_9505 4 144 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 144 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 144 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 144 169 (accept_3_3 2 144 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 169 (Polychromatic418967fa.accept_22_1_12_15_1_6077 1 144 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 169)))))))))))))))))))))))))) (allB_succ' 27 143 169
  (Eq.refl Bool.true) (allA_of_3_1 27 143 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 142 169 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 142 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 142 169 (accept_3_3 26 142 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 142 169 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 142 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 142 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 142 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 142 169 (accept_3_3 23 142 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 142 169 (Polychromatic418967fa.accept_14_8_2_1_1_1652 22 142 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 142 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 142 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 169 (accept_3_3 20 142 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 142 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 142 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 169
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 142 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 142 169 (accept_3_3 17 142 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 169 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 142 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 142 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 142 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 169 (accept_3_3 14 142 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 142 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 169
  (Polychromatic418967fa.accept_15_12_7_4_1_2921 12 142 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 142 169 (accept_3_3 11 142 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 142 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 142 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 142 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 142 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 169 (accept_3_3 8 142 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 142 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 169
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 142 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 169 (accept_3_3 5 142 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 142 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 142 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 169 (accept_3_3 2 142 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 169 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 142 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 169)))))))))))))))))))))))))))) (allB_succ' 29 141
  169 (Eq.refl Bool.true) (allA_succ_of_accept 28 141 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 141 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 169
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 141 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 141 169 (accept_3_3 26 141 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 141 169 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 141 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 141 169 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 141 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 169 (accept_3_3 23 141 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 141 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 141 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 141 169 (accept_3_3 20 141 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 141 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 141 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 141 169 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 141 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 169 (accept_3_3 17 141 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 141 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 169
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 141 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 141 169 (accept_3_3 14 141 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 141 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 141 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 141 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 141 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 169 (accept_3_3 11 141 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 141 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 169
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 141 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 141 169 (accept_3_3 8 141 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  141 169 (Polychromatic418967fa.accept_16_7_13_9_1_1653 7 141 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 141 169 (Polychromatic418967fa.accept_16_6_13_9_1_4690 6 141 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 169 (accept_3_3 5 141 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 141 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 141 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 141 169 (accept_3_3 2 141 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  141 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 141 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 141 169))))))))))))))))))))))))))))) (allB_succ' 30 140 169 (Eq.refl Bool.true) (allA_of_3_1 30
  140 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 139 169 (Eq.refl Bool.true) (allA_succ_of_accept 30
  139 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 139 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 139 169 (accept_3_3 29 139 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 139 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 139 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 169 (Polychromatic418967fa.accept_19_8_6_17_1_5186 27 139
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 169 (accept_3_3 26 139
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 169
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 25 139 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 139 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 139 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 169 (accept_3_3 23 139 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 139 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 139 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 21
  139 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 169 (accept_3_3 20
  139 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 169
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 139 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 139 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 139 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 169 (accept_3_3 17 139 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 139 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 139 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 169 (Polychromatic418967fa.accept_9_6_4_7_1_300
  15 139 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 169 (accept_3_3 14
  139 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 169
  (Polychromatic418967fa.accept_17_13_3_16_1_5599 13 139 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 139 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 169 (accept_3_3 11 139 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 139 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 169
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 139 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 169 (accept_3_3 8 139 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 169 (Polychromatic418967fa.accept_14_7_13_1_1_922 7 139 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 139 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 169 (accept_3_3 5 139 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 169 (Polychromatic418967fa.accept_16_4_11_9_1_1631 4 139 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 139 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 169 (accept_3_3 2 139 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 139 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 169))))))))))))))))))))))))))))))) (allB_succ' 32 138 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 31 138 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 138 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 138 169 (Polychromatic418967fa.accept_19_11_5_17_1_2620 30 138
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 138 169 (accept_3_3 29 138
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 169 (Polychromatic418967fa.accept_9_1_3_7_1_6
  28 138 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 138 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 138 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 138 169 (accept_3_3 26 138 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 138 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 138 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 138 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 138 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 138 169 (accept_3_3 23 138 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 138 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 138 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 138 169
  (Polychromatic418967fa.accept_10_1_8_9_1_787 21 138 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 138 169 (accept_3_3 20 138 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 138 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 138 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 138 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 138 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 138 169 (accept_3_3 17 138 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 169 (Polychromatic418967fa.accept_15_1_3_4_1_1217 16 138 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 138 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 138 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 138 169 (accept_3_3 14 138 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 138 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 138 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 138 169 (Polychromatic418967fa.accept_19_12_5_17_1_9439 12 138 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 138 169 (accept_3_3 11 138 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 138 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 169
  (Polychromatic418967fa.accept_21_9_12_1_1_7926 9 138 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 138 169 (accept_3_3 8 138 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  138 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 138 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 138 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 138 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 138 169 (accept_3_3 5 138 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 138 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 138 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 138 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 138 169 (accept_3_3 2 138 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  138 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 138 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 138 169)))))))))))))))))))))))))))))))) (allB_succ' 33 137 169 (Eq.refl Bool.true) (allA_of_3_1
  33 137 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 136 169 (Eq.refl Bool.true) (allA_succ_of_accept 33
  136 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 136 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 136 169 (accept_3_3 32 136 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 136 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 136 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 136 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 136 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 136 169 (accept_3_3 29 136 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 136 169
  (Polychromatic418967fa.accept_16_12_8_9_1_2583 28 136 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 136 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 136 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 136 169 (accept_3_3 26 136 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 136 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 136 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 136 169 (Polychromatic418967fa.accept_9_6_1_7_1_577
  24 136 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 136 169 (accept_3_3 23
  136 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 136 169
  (Polychromatic418967fa.accept_9_4_1_7_1_293 22 136 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 136 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 136 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 169 (accept_3_3 20 136 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 136 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 136 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 18
  136 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 136 169 (accept_3_3 17
  136 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 136 169
  (Polychromatic418967fa.accept_7_2_3_1_1_10 16 136 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 136 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 136 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 169 (accept_3_3 14 136 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 136 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 136 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 136 169 (Polychromatic418967fa.accept_7_5_3_1_1_424
  12 136 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 136 169 (accept_3_3 11
  136 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 136 169
  (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 136 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 136 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 169 (accept_3_3 8 136 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 136 169 (Polychromatic418967fa.accept_16_7_8_9_1_9427 7 136 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 136 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 6
  136 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 169 (accept_3_3 5 136
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 136 169 (Polychromatic418967fa.accept_7_4_3_1_1_87
  4 136 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 136 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 136 169 (accept_3_3 2 136 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  136 169 (Polychromatic418967fa.accept_16_1_8_9_1_3462 1 136 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 136 169)))))))))))))))))))))))))))))))))) (allB_succ' 35 135 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 34 135 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 135 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 169 (Polychromatic418967fa.accept_12_9_3_1_1_303 33 135
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 169 (accept_3_3 32 135
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 135 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 135 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 135 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 169 (accept_3_3 29 135 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 135 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 135 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 169 (Polychromatic418967fa.accept_7_6_2_1_1_214
  27 135 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 169 (accept_3_3 26
  135 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 169
  (Polychromatic418967fa.accept_20_5_15_9_1_9446 25 135 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 135 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 135 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 169 (accept_3_3 23 135 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 135 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 135 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 169 (Polychromatic418967fa.accept_10_1_5_9_1_157
  21 135 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 169 (accept_3_3 20
  135 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 169
  (Polychromatic418967fa.accept_16_3_7_9_1_3474 19 135 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 135 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 135 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 169 (accept_3_3 17 135 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 135 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 135 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 169
  (Polychromatic418967fa.accept_19_15_2_17_1_5163 15 135 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 135 169 (accept_3_3 14 135 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 135 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 169 (Polychromatic418967fa.accept_19_12_2_17_1_5210 12 135
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 169 (accept_3_3 11 135
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 169 (Polychromatic418967fa.accept_4_2_3_1_1_2
  10 135 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 169
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 135 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 135 169 (accept_3_3 8 135 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  135 169 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 135 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 135 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 135 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 169 (accept_3_3 5 135 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 135 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 135 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 169 (accept_3_3 2 135 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  135 169 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 135 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135 169))))))))))))))))))))))))))))))))))) (allB_succ' 36 134 169 (Eq.refl Bool.true)
  (allA_of_3_1 36 134 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 133 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 133 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 133 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 169 (accept_3_3 35 133 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 133 169 (Polychromatic418967fa.accept_10_4_3_9_1_1262 34 133 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 169
  (Polychromatic418967fa.accept_16_1_5_9_1_1649 33 133 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 169 (accept_3_3 32 133 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 169 (Polychromatic418967fa.accept_21_10_7_1_1_9464 31 133 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 169 (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 133 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 169 (accept_3_3 29 133 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 133 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 169
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 133 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 169 (accept_3_3 26 133 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 169 (Polychromatic418967fa.accept_15_10_13_4_1_1210 25 133 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 169 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 133 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 169 (accept_3_3 23 133 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 169 (Polychromatic418967fa.accept_14_8_7_1_1_1615 22 133
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 169
  (Polychromatic418967fa.accept_15_6_13_4_1_2040 21 133 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 169 (accept_3_3 20 133 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 169 (Polychromatic418967fa.accept_11_8_1_4_1_2318 19 133 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 169 (Polychromatic418967fa.accept_25_18_8_19_1_7580 18 133 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 169 (accept_3_3 17 133 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 169 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 133
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 169
  (Polychromatic418967fa.accept_17_15_14_16_1_5625 15 133 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 133 169 (accept_3_3 14 133 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 133 169 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 133 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 133 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 169 (accept_3_3 11 133 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 169
  (Polychromatic418967fa.accept_15_10_13_4_1_1210 10 133 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 169 (Polychromatic418967fa.accept_15_9_13_4_1_1209 9 133 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 169 (accept_3_3 8 133 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 169 (Polychromatic418967fa.accept_24_7_13_1_1_9522 7 133
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 169
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 133 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 169 (accept_3_3 5 133 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 133 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 169 (Polychromatic418967fa.accept_21_3_7_1_1_9521 3 133 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 169 (accept_3_3 2 133 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 169 (Polychromatic418967fa.accept_16_1_5_9_1_1649 1 133 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133 169))))))))))))))))))))))))))))))))))))) (allB_succ'
  38 132 169 (Eq.refl Bool.true) (allA_succ_of_accept 37 132 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 132 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 132 169
  (Polychromatic418967fa.accept_21_15_6_1_1_6306 36 132 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 132 169 (accept_3_3 35 132 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 132 169 (Polychromatic418967fa.accept_25_9_7_19_1_9520 34 132 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 132 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 132 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 169 (accept_3_3 32 132 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 132 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 132 169
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 132 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 132 169 (accept_3_3 29 132 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 132 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 132 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 132 169 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 132 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 169 (accept_3_3 26 132 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 132 169 (Polychromatic418967fa.accept_19_6_18_17_1_9518 25 132
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 132 169
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 24 132 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 132 169 (accept_3_3 23 132 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 132 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 132 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 132 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 132 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 169 (accept_3_3 20 132 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 132 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 132 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 132 169
  (Polychromatic418967fa.accept_24_18_12_1_1_9519 18 132 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 132 169 (accept_3_3 17 132 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 132 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 132 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 132 169 (Polychromatic418967fa.accept_21_15_6_1_1_6306 15 132
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 169 (accept_3_3 14 132
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 169
  (Polychromatic418967fa.accept_8_5_4_1_1_111 13 132 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 132 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 132 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 132 169 (accept_3_3 11 132 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 132 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 132 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 9
  132 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 169 (accept_3_3 8 132
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 169
  (Polychromatic418967fa.accept_10_7_2_9_1_775 7 132 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 132 169 (Polychromatic418967fa.accept_19_6_18_17_1_9518 6 132 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 132 169 (accept_3_3 5 132 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 132 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 132 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 3
  132 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 169 (accept_3_3 2 132
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 169
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 132 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 132 169)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 131 169 (Eq.refl Bool.true) (allA_of_3_1 39 131
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 130 169 (Eq.refl Bool.true) (allA_succ_of_gcd 39 130 169
  13 3 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 130
  169 (accept_3_3 38 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 130 169
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 130 169 (Polychromatic418967fa.accept_15_6_10_4_1_150 36 130 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 130 169 (accept_3_3 35 130 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 130 169 (Polychromatic418967fa.accept_18_16_4_7_1_2927 34 130 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 130 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 130 169 (accept_3_3 32 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 130 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 130 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 130 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 130 169 (accept_3_3 29 130 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 130 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 130 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 130 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 130 169 13 2 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 130 169 (Polychromatic418967fa.accept_14_11_4_1_1_4255 25 130 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 130 169
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 130 169 (accept_3_3 23 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 130 169 (Polychromatic418967fa.accept_15_7_10_4_1_151 22 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 130 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 130 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 130 169 (accept_3_3 20 130 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 130 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 130 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 130 169
  (Polychromatic418967fa.accept_19_18_16_17_1_2626 18 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 130 169 (accept_3_3 17 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 130 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 130 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 130 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 130 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 130 169 (accept_3_3 14 130 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 130 169 13 1 10 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 130 169
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 130 169 (accept_3_3 11 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 130 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 130 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 130 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 130 169 (accept_3_3 8 130 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 130 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 130 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 130 169 (accept_3_3 5 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  130 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 130 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 130 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 130 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 169 (accept_3_3 2 130 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 130 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 130 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130 169))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 129 169 (Eq.refl Bool.true) (allA_succ_of_accept 40 129 169 (Polychromatic418967fa.accept_6_4_3_1_1_57
  40 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 169
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 129 169 (accept_3_3 38 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 129 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 129 169 (Polychromatic418967fa.accept_15_6_9_4_1_1227 36 129 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 169 (accept_3_3 35 129 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 129 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 169
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 129 169 (accept_3_3 32 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 129 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 129 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 129 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 169 (accept_3_3 29 129 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 129 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 169
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 129 169 (accept_3_3 26 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 129 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 129 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 129 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 169 (accept_3_3 23 129 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 129 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 169
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 21 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 129 169 (accept_3_3 20 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 129 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 129 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 129 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 169 (accept_3_3 17 129 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 129 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 129 169 (accept_3_3 14 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 129 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 129 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 129 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 169 (accept_3_3 11 129 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 129 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 169
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 129 169 (accept_3_3 8 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  129 169 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 129 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 129 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 169 (accept_3_3 5 129 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 129 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 169
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 169 (accept_3_3 2 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 129 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129 169))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 128 169 (Eq.refl Bool.true)
  (allA_of_3_1 42 128 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 127 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 42 127 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 127 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 169 (accept_3_3 41 127 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 127 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 127 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 39
  127 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 169 (accept_3_3 38
  127 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 169
  (Polychromatic418967fa.accept_19_18_13_17_1_9517 37 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 127 169 (Polychromatic418967fa.accept_17_2_8_16_1_4403 36 127 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 169 (accept_3_3 35 127 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 127 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 169
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 169 (accept_3_3 32 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 127 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 169 (accept_3_3 29 127 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 169 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 127 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 169
  (Polychromatic418967fa.accept_15_12_7_4_1_2921 27 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 169 (accept_3_3 26 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 169 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 127 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 169 (accept_3_3 23 127 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 127 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 169
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 169 (accept_3_3 20 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 169 (Polychromatic418967fa.accept_17_2_8_16_1_4403 19 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 127 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 169 (accept_3_3 17 127 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 169 (Polychromatic418967fa.accept_18_16_1_7_1_4083 16 127 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 169
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 169 (accept_3_3 14 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 127 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 169 (accept_3_3 11 127 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 127 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 169
  (Polychromatic418967fa.accept_17_9_8_16_1_2176 9 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 169 (accept_3_3 8 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 169 (Polychromatic418967fa.accept_17_7_8_16_1_6966 7 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 127 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 169 (accept_3_3 5 127 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 127 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 169
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 169 (accept_3_3 2 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 169 (Polychromatic418967fa.accept_23_1_12_8_1_9477 1 127 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 169))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 126 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 126 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 126 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 126 169 (Polychromatic418967fa.accept_17_8_7_16_1_9508 42 126
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 126 169 (accept_3_3 41 126
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 169
  (Polychromatic418967fa.accept_15_10_6_4_1_1256 40 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 126 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 126 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 126 169 (accept_3_3 38 126 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 126 169 (Polychromatic418967fa.accept_16_5_14_9_1_2572 37 126 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 126 169
  (Polychromatic418967fa.accept_16_4_14_9_1_4657 36 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 126 169 (accept_3_3 35 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 126 169 (Polychromatic418967fa.accept_19_15_12_17_1_5195 34 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 126 169 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 126 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 126 169 (accept_3_3 32 126 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 126 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 126 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 126 169
  (Polychromatic418967fa.accept_20_10_6_9_1_4989 30 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 126 169 (accept_3_3 29 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 126 169 (Polychromatic418967fa.accept_15_13_6_4_1_1221 28 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 126 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 126 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 126 169 (accept_3_3 26 126 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 169 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 126 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 126 169
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 126 169 (accept_3_3 23 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 126 169 (Polychromatic418967fa.accept_19_3_12_17_1_6585 22 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 126 169 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 126 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 126 169 (accept_3_3 20 126 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 126 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 126 169
  (Polychromatic418967fa.accept_19_18_12_17_1_8026 18 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 126 169 (accept_3_3 17 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 126 169 (Polychromatic418967fa.accept_24_16_6_1_1_9516 16 126 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 126 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 126 169 (accept_3_3 14 126 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 169 (Polychromatic418967fa.accept_10_3_6_9_1_779
  13 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 126 169
  (Polychromatic418967fa.accept_23_12_11_8_1_9515 12 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 126 169 (accept_3_3 11 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 126 169 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 126 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 169 (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 126 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 169 (accept_3_3 8 126 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7
  126 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 126 169
  (Polychromatic418967fa.accept_17_6_7_16_1_6836 6 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 126 169 (accept_3_3 5 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  126 169 (Polychromatic418967fa.accept_16_4_14_9_1_4657 4 126 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 126 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 126 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 169 (accept_3_3 2 126 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 169 (Polychromatic418967fa.accept_22_1_16_15_1_9514 1 126 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 169))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 125 169 (Eq.refl Bool.true) (allA_of_3_1 45 125 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 124 169 (Eq.refl Bool.true) (allA_succ_of_accept 45 124 169 (Polychromatic418967fa.accept_6_3_4_1_1_8
  45 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 124 169 (accept_3_3 44
  124 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 124 169
  (Polychromatic418967fa.accept_10_3_4_9_1_15 43 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 124 169 (Polychromatic418967fa.accept_19_4_10_17_1_5194 42 124 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 124 169 (accept_3_3 41 124 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 124 169 (Polychromatic418967fa.accept_11_7_3_4_1_729 40 124 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 124 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 124 169 (accept_3_3 38 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 124 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 124 169 (Polychromatic418967fa.accept_16_4_12_9_1_2567 36 124 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 124 169 (accept_3_3 35 124 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 124 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 124 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 124 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 124 169 (accept_3_3 32 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 124 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 124 169 (Polychromatic418967fa.accept_23_7_9_8_1_9513 30 124 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 124 169 (accept_3_3 29 124 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 124 169 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 124
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 124 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 124 169 (accept_3_3 26 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 124 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 124 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 124 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 124 169 (accept_3_3 23 124 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 124 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 124 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 124 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 124 169 (accept_3_3 20 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 124 169 (Polychromatic418967fa.accept_16_3_12_9_1_8250 19 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 124 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 124 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 124 169 (accept_3_3 17 124 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 124 169 (Polychromatic418967fa.accept_21_16_19_1_1_6320 16 124 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 124 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 124 169 (accept_3_3 14 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 124 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 124 169 (Polychromatic418967fa.accept_19_12_10_17_1_5189 12 124 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 169 (accept_3_3 11 124 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 124 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 124 169 (accept_3_3 8 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  124 169 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 124 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 124 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 169 (accept_3_3 5 124 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 124 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 124 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 124 169 (accept_3_3 2 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  124 169 (Polychromatic418967fa.accept_17_1_5_16_1_5589 1 124 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 124 169)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 123 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 123 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 123 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 123 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 123 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 169 (accept_3_3 44 123 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 169
  (Polychromatic418967fa.accept_24_19_3_1_1_5907 43 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 123 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 123 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 169 (accept_3_3 41 123 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 123 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 123 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 123 169 (Polychromatic418967fa.accept_9_3_6_7_1_562
  39 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 169 (accept_3_3 38
  123 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 169
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 123 169 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 123 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 169 (accept_3_3 35 123 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 123 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 123 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 123 169 (Polychromatic418967fa.accept_7_5_4_1_1_412
  33 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 169 (accept_3_3 32
  123 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 169
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 123 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 123 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 169 (accept_3_3 29 123 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 123 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 123 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 123 169
  (Polychromatic418967fa.accept_19_8_9_17_1_5151 27 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 123 169 (accept_3_3 26 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 123 169 (Polychromatic418967fa.accept_19_6_9_17_1_5214 25 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 123 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 123 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 169 (accept_3_3 23 123 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 123 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 123 169 (accept_3_3 20 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 123 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 123 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 123 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 169 (accept_3_3 17 123 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 123 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 169
  (Polychromatic418967fa.accept_17_15_4_16_1_6890 15 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 169 (accept_3_3 14 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 123 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 123 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 123 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 169 (accept_3_3 11 123 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10
  123 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 169
  (Polychromatic418967fa.accept_11_9_2_4_1_707 9 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 123 169 (accept_3_3 8 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  123 169 (Polychromatic418967fa.accept_15_7_3_4_1_574 7 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 123 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 123 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 169 (accept_3_3 5 123 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 123 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 169
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 123 169 (accept_3_3 2 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  123 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 123 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 123 169))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 122 169 (Eq.refl
  Bool.true) (allA_of_3_1 48 122 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 121 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 121 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 121 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 169 (accept_3_3 47 121 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 121 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 121 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 169 (Polychromatic418967fa.accept_7_3_2_1_1_225
  45 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 121 169 (accept_3_3 44
  121 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 121 169
  (Polychromatic418967fa.accept_19_5_7_17_1_9442 43 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 121 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 121 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 169 (accept_3_3 41 121 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 121 169 (Polychromatic418967fa.accept_18_4_13_7_1_5395 40 121 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 169 (accept_3_3 38 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 169 (Polychromatic418967fa.accept_14_8_9_1_1_3313 36 121 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 169 (accept_3_3 35 121 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 121 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 169 (accept_3_3 32 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 121 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 169 (accept_3_3 29 121 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 121 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 169
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 169 (accept_3_3 26 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 169 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 121 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 169 (accept_3_3 23 121 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 169 (Polychromatic418967fa.accept_10_2_1_9_1_1248 22 121 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 169 (accept_3_3 20 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 169 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 121 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 169 (accept_3_3 17 121 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 169 (Polychromatic418967fa.accept_19_16_7_17_1_3853 16 121
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 169 (accept_3_3 14 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 121 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 169 (accept_3_3 11 121 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 121 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 169
  (Polychromatic418967fa.accept_19_9_7_17_1_3875 9 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 169 (accept_3_3 8 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 169 (Polychromatic418967fa.accept_21_7_16_1_1_6298 7 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 121 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 169 (accept_3_3 5 121 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 169 (Polychromatic418967fa.accept_18_4_13_7_1_5395 4 121 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 169 (accept_3_3 2 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 121 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 169))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 120 169 (Eq.refl
  Bool.true) (allA_succ_of_accept 49 120 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 120 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 120 169
  (Polychromatic418967fa.accept_21_6_15_1_1_2050 48 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 120 169 (accept_3_3 47 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 120 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 120 169 (Polychromatic418967fa.accept_21_3_15_1_1_2046 45 120 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 120 169 (accept_3_3 44 120 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 120 169 (Polychromatic418967fa.accept_23_20_5_8_1_9512 43 120
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 120 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 120 169 (accept_3_3 41 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 120 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 120 169 (Polychromatic418967fa.accept_16_7_8_9_1_9427 39 120 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 120 169 (accept_3_3 38 120 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 120 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 120 169
  (Polychromatic418967fa.accept_16_4_8_9_1_4639 36 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 120 169 (accept_3_3 35 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 120 169 (Polychromatic418967fa.accept_22_12_10_15_1_4511 34 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 120 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 169 (accept_3_3 32 120 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 120 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 120 169
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 30 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 120 169 (accept_3_3 29 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 120 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 120 169 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 120 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 169 (accept_3_3 26 120 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 169 (Polychromatic418967fa.accept_22_3_10_15_1_9511 25 120
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 120 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 120 169 (accept_3_3 23 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 120 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 120 169 (Polychromatic418967fa.accept_14_7_8_1_1_1621 21 120 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 169 (accept_3_3 20 120 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 120 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 120 169
  (Polychromatic418967fa.accept_19_18_6_17_1_8078 18 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 120 169 (accept_3_3 17 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 120 169 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 120 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 120 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 169 (accept_3_3 14 120 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 169 (Polychromatic418967fa.accept_9_4_3_7_1_296
  13 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 169
  (Polychromatic418967fa.accept_16_12_8_9_1_2583 12 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 120 169 (accept_3_3 11 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 120 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 120 169 (Polychromatic418967fa.accept_14_9_8_1_1_2381 9 120 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 169 (accept_3_3 8 120 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 169 (Polychromatic418967fa.accept_14_7_8_1_1_1621 7 120 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 120 169 (accept_3_3 5 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  120 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 120 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 120 169 (Polychromatic418967fa.accept_18_3_12_7_1_6728 3 120 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 169 (accept_3_3 2 120 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 120 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  169)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 119 169 (Eq.refl Bool.true) (allA_of_3_1 51 119
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 118 169 (Eq.refl Bool.true) (allA_succ_of_accept 51 118
  169 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 118 169 (accept_3_3 50 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 118 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 118 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 118 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 118 169 (accept_3_3 47 118 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 118 169 (Polychromatic418967fa.accept_19_8_4_17_1_9510 46 118 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 118 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 118 169 (accept_3_3 44 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 118 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 118 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 118 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 118 169 (accept_3_3 41 118 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 118 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 118 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 118 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 118 169 (accept_3_3 38 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 118 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 118 169 (Polychromatic418967fa.accept_15_6_13_4_1_2040 36 118 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 118 169 (accept_3_3 35 118 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 118 169 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 118
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 118 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 118 169 (accept_3_3 32 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 118 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 118 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 118 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 118 169 (accept_3_3 29 118 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 118 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 118 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 118 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 118 169 (accept_3_3 26 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 118 169 (Polychromatic418967fa.accept_15_10_13_4_1_1210 25 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 118 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 118 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 118 169 (accept_3_3 23 118 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 118 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 118 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 118 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 118 169 (accept_3_3 20 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 118 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 118 169 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 118 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 118 169 (accept_3_3 17 118 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 118 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 118 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 118 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 118 169 (accept_3_3 14 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 118 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 118 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 118 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 118 169 (accept_3_3 11 118 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 118 169 (Polychromatic418967fa.accept_15_10_13_4_1_1210 10 118 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 118 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 118 169 (accept_3_3 8 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  118 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 118 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 118 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 118 169 (accept_3_3 5 118 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 118 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 118 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 118 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 118 169 (accept_3_3 2 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  118 169 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 118 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 118 169)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 117 169 (Eq.refl
  Bool.true) (allA_succ_of_gcd 52 117 169 13 4 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 117 169 (Polychromatic418967fa.accept_12_3_9_1_1_290 51 117 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 169 (accept_3_3 50 117 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 169 (Polychromatic418967fa.accept_16_1_5_9_1_1649 49 117 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 169
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 117 169 (accept_3_3 47 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 117 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 117 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 117 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 169 (accept_3_3 44 117 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 169 (Polychromatic418967fa.accept_16_11_5_9_1_1617 43 117 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 169
  (Polychromatic418967fa.accept_10_2_7_9_1_783 42 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 117 169 (accept_3_3 41 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 117 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 117 169 13 3 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 117 169 (accept_3_3 38 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 169 (Polychromatic418967fa.accept_15_7_12_4_1_1236 37 117 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 117 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 169 (accept_3_3 35 117 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 34
  117 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 169
  (Polychromatic418967fa.accept_16_1_5_9_1_1649 33 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 117 169 (accept_3_3 32 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 117 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 117 169 (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 117 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 169 (accept_3_3 29 117 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 117 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 169
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 117 169 13 2 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 117 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 117 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 117 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 169 (accept_3_3 23 117 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 22
  117 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 169
  (Polychromatic418967fa.accept_17_4_15_16_1_3231 21 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 169 (accept_3_3 20 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 169 (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 117 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 117 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 169 (accept_3_3 17 117 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  117 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 169
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 117 169 (accept_3_3 14 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13
  117 169 13 1 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  12 117 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 169 (accept_3_3 11 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 117 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 169 (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 117
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 169 (accept_3_3 8 117 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 169 (Polychromatic418967fa.accept_15_7_12_4_1_1236
  7 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 169
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 169 (accept_3_3 5 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 117 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 169 (accept_3_3 2 117 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 169 (Polychromatic418967fa.accept_15_1_12_4_1_2022 1 117 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  169))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 116 169 (Eq.refl Bool.true) (allA_of_3_1 54
  116 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 115 169 (Eq.refl Bool.true) (allA_succ_of_accept 54
  115 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 115 169 (accept_3_3 53 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 115 169 (Polychromatic418967fa.accept_15_7_10_4_1_151 52 115 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 115 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 169 (accept_3_3 50 115 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 115 169
  (Polychromatic418967fa.accept_21_7_10_1_1_6278 49 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 115 169 (Polychromatic418967fa.accept_19_10_1_17_1_6595 48 115 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 169 (accept_3_3 47 115 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 115 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 115 169
  (Polychromatic418967fa.accept_20_5_15_9_1_9446 45 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 115 169 (accept_3_3 44 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 169 (Polychromatic418967fa.accept_11_10_5_4_1_711 43 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 115 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 169 (accept_3_3 41 115 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 115 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 169
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 115 169 (accept_3_3 38 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 115 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 169 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 115 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 169 (accept_3_3 35 115 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 115 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 169
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 169 (accept_3_3 32 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 169 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 115 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 115 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 169 (accept_3_3 29 115 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 169 (Polychromatic418967fa.accept_15_13_10_4_1_1232 28 115 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 169
  (Polychromatic418967fa.accept_24_3_19_1_1_9509 27 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 115 169 (accept_3_3 26 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 115 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 115 169 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 115 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 169 (accept_3_3 23 115 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 115 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 169
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 169 (accept_3_3 20 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 115 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 169 (accept_3_3 17 115 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 115 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 169
  (Polychromatic418967fa.accept_19_15_1_17_1_670 15 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 169 (accept_3_3 14 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 169 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 115 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 169 (accept_3_3 11 115 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 115 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 169
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 169 (accept_3_3 8 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 169 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 115 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 169 (accept_3_3 5 115 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 115 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 169
  (Polychromatic418967fa.accept_17_3_13_16_1_2183 3 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 169 (accept_3_3 2 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 169 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 115 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115 169))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 114 169 (Eq.refl
  Bool.true) (allA_succ_of_accept 55 114 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 114 169 (Polychromatic418967fa.accept_16_6_2_9_1_5897
  54 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 114 169 (accept_3_3 53
  114 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 52 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 114 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 114 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 169 (accept_3_3 50 114 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 114 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 114 169 (Polychromatic418967fa.accept_7_6_2_1_1_214
  48 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 114 169 (accept_3_3 47
  114 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 169
  (Polychromatic418967fa.accept_9_1_6_7_1_285 46 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 114 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 114 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 169 (accept_3_3 44 114 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 114 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 114 169
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 42 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 114 169 (accept_3_3 41 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 114 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 114 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 169 (accept_3_3 38 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 114 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 169
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 114 169 (accept_3_3 35 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 114 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 114 169 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 169 (accept_3_3 32 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 114 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 114 169 (accept_3_3 29 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 114 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 114 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 169 (accept_3_3 26 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 169 (Polychromatic418967fa.accept_10_5_4_9_1_420 25 114 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 114 169 (accept_3_3 23 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 114 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 114 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 169 (accept_3_3 20 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 114 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 169
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 114 169 (accept_3_3 17 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 114 169 (Polychromatic418967fa.accept_22_16_4_15_1_7881 16 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 114 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 169 (accept_3_3 14 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 114 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 114 169 (accept_3_3 11 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 114 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 114 169 (Polychromatic418967fa.accept_18_9_6_7_1_6719 9 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 169 (accept_3_3 8 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 114 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 169
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 114 169 (accept_3_3 5 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  114 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 114 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 114 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 169 (accept_3_3 2 114 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 114 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  169)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 113 169 (Eq.refl Bool.true) (allA_of_3_1 57
  113 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 112 169 (Eq.refl Bool.true) (allA_succ_of_accept 57
  112 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 112 169 (accept_3_3 56 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 112 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 112 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 112 169 (Polychromatic418967fa.accept_21_12_7_1_1_9465 54 112
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 112 169 (accept_3_3 53 112
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 112 169
  (Polychromatic418967fa.accept_18_16_4_7_1_2927 52 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 112 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 112 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 112 169 (accept_3_3 50 112 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 112 169 (Polychromatic418967fa.accept_18_13_4_7_1_4086 49 112 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 112 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 112 169 (accept_3_3 47 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 112 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 112 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 112 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 112 169 (accept_3_3 44 112 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 112 169 (Polychromatic418967fa.accept_17_9_10_16_1_3217 43 112 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 112 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 112 169 (accept_3_3 41 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 112 169 (Polychromatic418967fa.accept_15_10_7_4_1_1222 40 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 112 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 112 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 112 169 (accept_3_3 38 112 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 112 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 112 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 112 169
  (Polychromatic418967fa.accept_21_15_7_1_1_6326 36 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 112 169 (accept_3_3 35 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 112 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 112 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 112 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 112 169 (accept_3_3 32 112 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 112 169 (Polychromatic418967fa.accept_10_1_2_9_1_152 31 112 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 112 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 112 169 (accept_3_3 29 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 112 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 112 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 112 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 112 169 (accept_3_3 26 112 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 112 169 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 112 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 112 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 112 169 (accept_3_3 23 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 112 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 112 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 112 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 112 169 (accept_3_3 20 112 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 112 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 112 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 112 169
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 112 169 (accept_3_3 17 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 112 169 (Polychromatic418967fa.accept_18_16_4_7_1_2927 16 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 112 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 112 169 (accept_3_3 14 112 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 112 169 (Polychromatic418967fa.accept_18_13_4_7_1_4086 13 112 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 112 169 (accept_3_3 11 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 112 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 112 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 169 (accept_3_3 8 112 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 112 169 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 112 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 112 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 112 169 (accept_3_3 5 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  112 169 (Polychromatic418967fa.accept_21_4_7_1_1_6307 4 112 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 112 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 169 (accept_3_3 2 112 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 112 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 112 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 111 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 111 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 111 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 169 (Polychromatic418967fa.accept_12_9_3_1_1_303 57 111
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 169 (accept_3_3 56 111
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 169 (Polychromatic418967fa.accept_9_1_3_7_1_6
  55 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 111 169 (accept_3_3 53 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 111 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 111 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 111 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 169 (accept_3_3 50 111 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 111 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 169
  (Polychromatic418967fa.accept_10_8_1_9_1_413 48 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 111 169 (accept_3_3 47 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 111 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 111 169 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 111 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 169 (accept_3_3 44 111 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 169 (Polychromatic418967fa.accept_15_13_6_4_1_1221 43 111
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 169 (accept_3_3 41 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 169 (Polychromatic418967fa.accept_15_9_6_4_1_1220 39 111 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 169 (accept_3_3 38 111 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 111 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 169
  (Polychromatic418967fa.accept_21_15_6_1_1_6306 36 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 111 169 (accept_3_3 35 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 111 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 111 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 111 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 169 (accept_3_3 32 111 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 111 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 169 (accept_3_3 29 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 169 (Polychromatic418967fa.accept_17_10_9_16_1_5607 27 111 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 169 (accept_3_3 26 111 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 169 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 111
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 169 (accept_3_3 23 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 169 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 111 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 169 (accept_3_3 20 111 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 111 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 169 (accept_3_3 17 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 111 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 169 (accept_3_3 14 111 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 111 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 169
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 111 169 (accept_3_3 11 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 111 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 111 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 111 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 169 (accept_3_3 8 111 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 169 (Polychromatic418967fa.accept_14_7_13_1_1_922 7 111 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 169 (accept_3_3 5 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 169 (Polychromatic418967fa.accept_19_3_16_17_1_3826 3 111 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 169 (accept_3_3 2 111 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 111 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 110 169 (Eq.refl Bool.true) (allA_of_3_1
  60 110 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 109 169 (Eq.refl Bool.true) (allA_succ_of_accept 60
  109 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 109 169 (accept_3_3 59 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 109 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 109 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 109 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 109 169 (accept_3_3 56 109 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 109 169
  (Polychromatic418967fa.accept_16_7_13_9_1_1653 55 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 109 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 109 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 169 (accept_3_3 53 109 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 109 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 109 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 169 (Polychromatic418967fa.accept_9_6_1_7_1_577
  51 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 169 (accept_3_3 50
  109 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 169
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 109 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 109 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 169 (accept_3_3 47 109 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 109 169 (Polychromatic418967fa.accept_14_4_11_1_1_940 46 109 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 169
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 169 (accept_3_3 44 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 169 (Polychromatic418967fa.accept_19_5_14_17_1_6550 43 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 109 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 169 (accept_3_3 41 109 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 109 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 169
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 169 (accept_3_3 38 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 169 (Polychromatic418967fa.accept_16_5_13_9_1_2594 37 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 109 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 169 (accept_3_3 35 109 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 169 (Polychromatic418967fa.accept_18_16_1_7_1_4083 34 109 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 169
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 169 (accept_3_3 32 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 109 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 169 (accept_3_3 29 109 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 109 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 169
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 169 (accept_3_3 26 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 169 (Polychromatic418967fa.accept_17_8_7_16_1_9508 25 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 109 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 169 (accept_3_3 23 109 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 109 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 169
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 169 (accept_3_3 20 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 169 (Polychromatic418967fa.accept_14_4_11_1_1_940 18 109 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 169 (accept_3_3 17 109 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 169 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 109
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 169
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 169 (accept_3_3 14 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 109 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 169 (accept_3_3 11 109 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 109 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 169
  (Polychromatic418967fa.accept_19_9_14_17_1_2613 9 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 169 (accept_3_3 8 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 169 (Polychromatic418967fa.accept_16_7_13_9_1_1653 7 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 109 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 169 (accept_3_3 5 109 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 109 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 169
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 169 (accept_3_3 2 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 169 (Polychromatic418967fa.accept_16_1_13_9_1_2551 1 109 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 108 169
  (Eq.refl Bool.true) (allA_succ_of_accept 61 108 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 108 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 108 169
  (Polychromatic418967fa.accept_7_4_3_1_1_87 60 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 108 169 (accept_3_3 59 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 108 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 108 169 (Polychromatic418967fa.accept_10_7_8_9_1_785 57 108 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 169 (accept_3_3 56 108 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 169 (Polychromatic418967fa.accept_26_3_4_13_1_9507 55 108
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 108 169
  (Polychromatic418967fa.accept_7_5_3_1_1_424 54 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 108 169 (accept_3_3 53 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 108 169 (Polychromatic418967fa.accept_15_7_3_4_1_574 52 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 108 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 108 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 169 (accept_3_3 50 108 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 169 (Polychromatic418967fa.accept_19_11_13_17_1_9466 49 108 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 108 169
  (Polychromatic418967fa.accept_21_6_3_1_1_6286 48 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 108 169 (accept_3_3 47 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 108 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 108 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 108 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 169 (accept_3_3 44 108 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 169 (Polychromatic418967fa.accept_17_9_6_16_1_3280 43 108 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 108 169
  (Polychromatic418967fa.accept_19_4_13_17_1_5137 42 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 108 169 (accept_3_3 41 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 108 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 108 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 108 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 169 (accept_3_3 38 108 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 37
  108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 108 169
  (Polychromatic418967fa.accept_16_4_12_9_1_2567 36 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 108 169 (accept_3_3 35 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 108 169 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 108 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 108 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 169 (accept_3_3 32 108 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 169 (Polychromatic418967fa.accept_10_1_8_9_1_787 31 108 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 169
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 108 169 (accept_3_3 29 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 108 169 (Polychromatic418967fa.accept_19_9_13_17_1_9506 28 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 108 169 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 108 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 169 (accept_3_3 26 108 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 108 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 108 169
  (Polychromatic418967fa.accept_10_4_8_9_1_784 24 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 108 169 (accept_3_3 23 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 108 169 (Polychromatic418967fa.accept_15_7_3_4_1_574 22 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 108 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 108 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 169 (accept_3_3 20 108 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 108 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 169
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 108 169 (accept_3_3 17 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 108 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 108 169 (Polychromatic418967fa.accept_19_15_13_17_1_5172 15 108 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 169 (accept_3_3 14 108 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 108 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 169
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 108 169 (accept_3_3 11 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 108 169 (Polychromatic418967fa.accept_17_10_6_16_1_6862 10 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 108 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 108 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 169 (accept_3_3 8 108 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 169 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 108 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 169
  (Polychromatic418967fa.accept_19_6_13_17_1_8015 6 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 108 169 (accept_3_3 5 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  108 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 108 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 108 169 (Polychromatic418967fa.accept_16_3_12_9_1_8250 3 108 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 169 (accept_3_3 2 108 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 169 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 108 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 107 169 (Eq.refl Bool.true)
  (allA_of_3_1 63 107 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 106 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 106 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 106 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 169 (accept_3_3 62 106 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 106 169 (Polychromatic418967fa.accept_19_4_11_17_1_9505 61 106 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 106 169
  (Polychromatic418967fa.accept_26_8_2_13_1_9504 60 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 106 169 (accept_3_3 59 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 106 169 (Polychromatic418967fa.accept_11_3_7_4_1_1133 58 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 106 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 169 (accept_3_3 56 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 106 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 169
  (Polychromatic418967fa.accept_17_3_4_16_1_3208 54 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 106 169 (accept_3_3 53 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 106 169 (Polychromatic418967fa.accept_11_8_7_4_1_3011 52 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 106 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 169 (accept_3_3 50 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 169 (Polychromatic418967fa.accept_14_7_8_1_1_1621 49 106 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 169
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 48 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 106 169 (accept_3_3 47 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 106 169 (Polychromatic418967fa.accept_19_8_11_17_1_9503 46 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 106 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 169 (accept_3_3 44 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 106 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 169
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 42 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 169 (accept_3_3 41 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 169 (accept_3_3 38 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 169 (Polychromatic418967fa.accept_14_9_8_1_1_2381 37 106 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 169
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 106 169 (accept_3_3 35 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 106 169 (Polychromatic418967fa.accept_20_14_6_9_1_9460 34 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 106 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 169 (accept_3_3 32 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 106 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 169
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 169 (accept_3_3 29 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 169 (accept_3_3 26 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 169 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 106 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 169
  (Polychromatic418967fa.accept_19_5_11_17_1_6536 24 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 106 169 (accept_3_3 23 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 106 169 (Polychromatic418967fa.accept_17_5_4_16_1_6925 22 106 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 106 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 106 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 169 (accept_3_3 20 106 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19
  106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 169
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 169 (accept_3_3 17 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 169 (accept_3_3 14 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 169 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 106 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 169
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 12 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 169 (accept_3_3 11 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 169 (Polychromatic418967fa.accept_20_10_6_9_1_4989 10 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 169 (accept_3_3 8 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 106 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 169
  (Polychromatic418967fa.accept_19_6_11_17_1_2611 6 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 169 (accept_3_3 5 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 106 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 169 (accept_3_3 2 106 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 169 (Polychromatic418967fa.accept_16_1_10_9_1_4645 1 106 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 105 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 64 105 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 105 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 105 169 (Polychromatic418967fa.accept_12_3_9_1_1_290 63 105
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 169 (accept_3_3 62 105
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 169
  (Polychromatic418967fa.accept_10_1_5_9_1_157 61 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 105 169 (Polychromatic418967fa.accept_22_16_17_15_1_9502 60 105 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 169 (accept_3_3 59 105 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 105 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 105 169 (accept_3_3 56 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 105 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 105 169 (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 105 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 169 (accept_3_3 53 105 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 105 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 169
  (Polychromatic418967fa.accept_10_1_5_9_1_157 51 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 105 169 (accept_3_3 50 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 105 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 105 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 105 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 169 (accept_3_3 47 105 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 105 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 169
  (Polychromatic418967fa.accept_19_7_10_17_1_8088 45 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 105 169 (accept_3_3 44 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 169 (Polychromatic418967fa.accept_24_19_9_1_1_9501 43 105 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 169 (Polychromatic418967fa.accept_19_4_10_17_1_5194 42 105
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 169 (accept_3_3 41 105
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 169
  (Polychromatic418967fa.accept_6_4_3_1_1_57 40 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 105 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 105 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 169 (accept_3_3 38 105 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 105 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 105 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 169 (Polychromatic418967fa.accept_10_6_5_9_1_1233
  36 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 169 (accept_3_3 35
  105 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 169
  (Polychromatic418967fa.accept_6_4_3_1_1_57 34 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 105 169 (Polychromatic418967fa.accept_22_11_17_15_1_9500 33 105 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 169 (accept_3_3 32 105 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 105 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 169 (accept_3_3 29 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 105 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 105 169 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 105 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 169 (accept_3_3 26 105 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 169 (Polychromatic418967fa.accept_26_25_1_13_1_9499 25 105
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 169
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 169 (accept_3_3 23 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 105 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 105 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 105 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 169 (accept_3_3 20 105 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 105 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 169
  (Polychromatic418967fa.accept_19_18_10_17_1_5192 18 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 105 169 (accept_3_3 17 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 169 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 105
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 169 (accept_3_3 14 105
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 169
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 105 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 105 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 169 (accept_3_3 11 105 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 105 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 105 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 169 (Polychromatic418967fa.accept_26_9_1_13_1_9498
  9 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 169 (accept_3_3 8
  105 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 169
  (Polychromatic418967fa.accept_17_7_3_16_1_2208 7 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 105 169 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 105 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 169 (accept_3_3 5 105 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 105 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 3
  105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 169 (accept_3_3 2 105
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 169
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 105 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 105 169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 104 169 (Eq.refl
  Bool.true) (allA_of_3_1 66 104 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 103 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 103 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 103 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 169 (accept_3_3 65 103 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 103 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 169
  (Polychromatic418967fa.accept_17_12_1_16_1_4360 63 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 103 169 (accept_3_3 62 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 103 169 (Polychromatic418967fa.accept_16_13_7_9_1_2606 61 103 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 103 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 169 (accept_3_3 59 103 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 58
  103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 169 (accept_3_3 56 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 169 (accept_3_3 53 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 103 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 51 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 169 (accept_3_3 50 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 169 (Polychromatic418967fa.accept_17_15_1_16_1_8166 49 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 169 (accept_3_3 47 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 103 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 169
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 169 (accept_3_3 44 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 169 (Polychromatic418967fa.accept_23_20_11_8_1_7798 43 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 169 (accept_3_3 41 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 169 (Polychromatic418967fa.accept_15_10_13_4_1_1210 40 103 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 169
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 169 (accept_3_3 38 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 169 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 103 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 169 (accept_3_3 35 103 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 103 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 169 (accept_3_3 32 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 169 (accept_3_3 29 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 103 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 169
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 169 (accept_3_3 26 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 169 (accept_3_3 23 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 103 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 169 (accept_3_3 20 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 169 (accept_3_3 17 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 169 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 103 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 169 (accept_3_3 14 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 169 (accept_3_3 11 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 103 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 169
  (Polychromatic418967fa.accept_15_9_13_4_1_1209 9 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 169 (accept_3_3 8 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 169 (Polychromatic418967fa.accept_21_7_19_1_1_9497 7 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 169 (accept_3_3 5 103 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 103 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 169
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 169 (accept_3_3 2 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 103 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 102
  169 (Eq.refl Bool.true) (allA_succ_of_accept 67 102 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 102 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 169
  (Polychromatic418967fa.accept_7_3_4_1_1_71 66 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 102 169 (accept_3_3 65 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 102 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 102 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 102 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 169 (accept_3_3 62 102 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 102 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 102 169 (accept_3_3 59 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 102 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 102 169 (Polychromatic418967fa.accept_10_7_2_9_1_775 57 102 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 169 (accept_3_3 56 102 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 102 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 169
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 102 169 (accept_3_3 53 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 102 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 102 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 102 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 169 (accept_3_3 50 102 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 102 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 169
  (Polychromatic418967fa.accept_19_10_7_17_1_9496 48 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 102 169 (accept_3_3 47 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 102 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 102 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 102 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 169 (accept_3_3 44 102 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 43
  102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 102 169 (accept_3_3 41 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 102 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 102 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 169 (accept_3_3 38 102 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 102 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 169
  (Polychromatic418967fa.accept_21_15_18_1_1_6300 36 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 102 169 (accept_3_3 35 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 102 169 (Polychromatic418967fa.accept_16_2_6_9_1_3473 34 102 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 102 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 169 (accept_3_3 32 102 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 169
  (Polychromatic418967fa.accept_21_9_18_1_1_9424 30 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 102 169 (accept_3_3 29 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 102 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 102 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 169 (accept_3_3 26 102 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 169 (Polychromatic418967fa.accept_14_11_4_1_1_4255 25 102 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 169
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 102 169 (accept_3_3 23 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 102 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 102 169 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 102 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 169 (accept_3_3 20 102 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 102 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 169
  (Polychromatic418967fa.accept_11_7_3_4_1_729 18 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 102 169 (accept_3_3 17 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 102 169 (Polychromatic418967fa.accept_15_1_12_4_1_2022 16 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 102 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 169 (accept_3_3 14 102 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 102 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 169
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 102 169 (accept_3_3 11 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 102 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 102 169 (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 102 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 169 (accept_3_3 8 102 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 102 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 169 (accept_3_3 5 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 102 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 169 (accept_3_3 2 102 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 102 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 101 169 (Eq.refl Bool.true)
  (allA_of_3_1 69 101 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 100 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 100 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 100 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 100 169 (accept_3_3 68 100 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 100 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 100 169 (Polychromatic418967fa.accept_7_3_2_1_1_225
  66 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 100 169 (accept_3_3 65
  100 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 100 169
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 64 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 100 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 100 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 100 169 (accept_3_3 62 100 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 100 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 100 169 (Polychromatic418967fa.accept_9_6_1_7_1_577
  60 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 100 169 (accept_3_3 59
  100 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 100 169
  (Polychromatic418967fa.accept_9_4_1_7_1_293 58 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 100 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 100 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 100 169 (accept_3_3 56 100 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 100 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 100 169
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 54 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 100 169 (accept_3_3 53 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 100 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 100 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 100 169 (accept_3_3 50 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 100 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 100 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 100 169
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 100 169 (accept_3_3 47 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 100 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 100 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 100 169 (accept_3_3 44 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 100 169 (Polychromatic418967fa.accept_15_13_10_4_1_1232 43 100 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 100 169
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 100 169 (accept_3_3 41 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 100 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 100 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 100 169 (accept_3_3 38 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 100 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 100 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 100 169
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 100 169 (accept_3_3 35 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 100 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 100 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 100 169 (accept_3_3 32 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 100 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 100 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 100 169
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 100 169 (accept_3_3 29 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 100 169 (Polychromatic418967fa.accept_15_13_10_4_1_1232 28 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 100 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 100 169 (accept_3_3 26 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 100 169 (Polychromatic418967fa.accept_22_3_12_15_1_9471 25 100 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 100 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 100 169 (accept_3_3 23 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 100 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 100 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 100 169 (accept_3_3 20 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 100 169 (Polychromatic418967fa.accept_11_8_1_4_1_2318 19 100 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 100 169
  (Polychromatic418967fa.accept_17_1_15_16_1_2202 18 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 100 169 (accept_3_3 17 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 100 169 (Polychromatic418967fa.accept_26_16_22_13_1_9495 16 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 100 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 15
  100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 100 169 (accept_3_3 14
  100 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 100 169
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 100 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 100 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 169 (accept_3_3 11 100 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 100 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 100 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 9
  100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 100 169 (accept_3_3 8 100
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 100 169
  (Polychromatic418967fa.accept_15_7_10_4_1_151 7 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 100 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 100 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 169 (accept_3_3 5 100 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 100 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 100 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 3
  100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 169 (accept_3_3 2 100
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 100 169
  (Polychromatic418967fa.accept_17_1_15_16_1_2202 1 100 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 100 169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 99 169 (Eq.refl
  Bool.true) (allA_succ_of_accept 70 99 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 99 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 169 (Polychromatic418967fa.accept_12_9_3_1_1_303
  69 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 169 (accept_3_3 68
  99 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 169
  (Polychromatic418967fa.accept_19_10_4_17_1_1544 67 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 99 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 99 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 169 (accept_3_3 65 99 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 99 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 99 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 169 (Polychromatic418967fa.accept_19_6_4_17_1_6540
  63 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 169 (accept_3_3 62
  99 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 169
  (Polychromatic418967fa.accept_21_19_15_1_1_6345 61 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 99 169 (Polychromatic418967fa.accept_16_12_3_9_1_5886 60 99 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 169 (accept_3_3 59 99 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 99 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 99 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 169 (Polychromatic418967fa.accept_12_9_3_1_1_303
  57 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 169 (accept_3_3 56
  99 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 169
  (Polychromatic418967fa.accept_15_10_9_4_1_2924 55 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 99 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 99 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 169 (accept_3_3 53 99 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 99 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 99 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 169 (Polychromatic418967fa.accept_15_6_9_4_1_1227
  51 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 169 (accept_3_3 50
  99 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 169
  (Polychromatic418967fa.accept_17_15_14_16_1_5625 49 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 169 (Polychromatic418967fa.accept_19_10_4_17_1_1544 48 99 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 169 (accept_3_3 47 99 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 99 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 169
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 169 (accept_3_3 44 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  99 169 (Polychromatic418967fa.accept_15_13_9_4_1_3892 43 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 169 (accept_3_3 41 99 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 99 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 169
  (Polychromatic418967fa.accept_16_7_3_9_1_2557 39 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 169 (accept_3_3 38 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 169 (Polychromatic418967fa.accept_19_18_4_17_1_2618 37 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 169 (Polychromatic418967fa.accept_15_6_9_4_1_1227 36 99 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 169 (accept_3_3 35 99 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 169
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 169 (accept_3_3 32 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 169 (Polychromatic418967fa.accept_21_10_15_1_1_9494 31 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 169 (accept_3_3 29 99 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 169
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 27 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 169 (accept_3_3 26 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 169 (Polychromatic418967fa.accept_15_10_9_4_1_2924 25 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 169 (Polychromatic418967fa.accept_18_6_9_7_1_2905 24 99 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 169 (accept_3_3 23 99 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 169
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 169 (accept_3_3 20 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 169 (Polychromatic418967fa.accept_17_2_14_16_1_2187 19 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 169 (accept_3_3 17 99 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 169
  (Polychromatic418967fa.accept_17_15_14_16_1_5625 15 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 169 (accept_3_3 14 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 169 (Polychromatic418967fa.accept_15_13_9_4_1_3892 13 99 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 169 (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 99
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 169 (accept_3_3 11 99 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10
  99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 169
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 169 (accept_3_3 8 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  169 (Polychromatic418967fa.accept_16_7_3_9_1_2557 7 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 169 (accept_3_3 5 99 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 169
  (Polychromatic418967fa.accept_18_3_9_7_1_1839 3 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 169 (accept_3_3 2 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  169 (Polychromatic418967fa.accept_19_1_4_17_1_5136 1 99 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 98
  169 (Eq.refl Bool.true) (allA_of_3_1 72 98 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 97 169 (Eq.refl
  Bool.true) (allA_succ_of_accept 72 97 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 97 169 (accept_3_3 71 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 97 169 (Polychromatic418967fa.accept_15_10_7_4_1_1222 70 97 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 97 169
  (Polychromatic418967fa.accept_16_5_1_9_1_4621 69 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 97 169 (accept_3_3 68 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  97 169 (Polychromatic418967fa.accept_19_10_2_17_1_675 67 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 97 169 (Polychromatic418967fa.accept_16_2_1_9_1_2577 66 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 169 (accept_3_3 65 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 169 (Polychromatic418967fa.accept_17_13_12_16_1_6908 64 97 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 97 169
  (Polychromatic418967fa.accept_14_7_13_1_1_922 63 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 97 169 (accept_3_3 62 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  97 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 97 169 (Polychromatic418967fa.accept_19_3_2_17_1_6574 60 97 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 169 (accept_3_3 59 97 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 97 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 169
  (Polychromatic418967fa.accept_11_2_9_4_1_310 57 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 169 (accept_3_3 56 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 169 (Polychromatic418967fa.accept_15_10_7_4_1_1222 55 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 169 (accept_3_3 53 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 169 (Polychromatic418967fa.accept_10_2_7_9_1_783 52 97 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 169
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 169 (accept_3_3 50 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 169 (Polychromatic418967fa.accept_14_7_13_1_1_922 49 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 169 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 169 (accept_3_3 47 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 169 (Polychromatic418967fa.accept_11_2_9_4_1_310 46 97 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 169
  (Polychromatic418967fa.accept_16_13_1_9_1_2597 45 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 169 (accept_3_3 44 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 169 (Polychromatic418967fa.accept_19_5_2_17_1_8066 43 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 169 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 169 (accept_3_3 41 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 97 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 169
  (Polychromatic418967fa.accept_25_14_22_19_1_9493 39 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 97 169 (accept_3_3 38 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 97 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 97 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 169 (Polychromatic418967fa.accept_23_13_5_8_1_9492 36 97
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 169 (accept_3_3 35 97 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 169 (Polychromatic418967fa.accept_16_2_1_9_1_2577
  34 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 169
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 169 (accept_3_3 32 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 169 (Polychromatic418967fa.accept_19_12_2_17_1_5210 31 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 169 (accept_3_3 29 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 169 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 97 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 169
  (Polychromatic418967fa.accept_15_12_7_4_1_2921 27 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 169 (accept_3_3 26 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 169 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 169 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 169 (accept_3_3 23 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 169 (Polychromatic418967fa.accept_10_2_7_9_1_783 22 97 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 169
  (Polychromatic418967fa.accept_14_7_13_1_1_922 21 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 169 (accept_3_3 20 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 169 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 169 (accept_3_3 17 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 97 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 169
  (Polychromatic418967fa.accept_19_15_2_17_1_5163 15 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 169 (accept_3_3 14 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 169 (Polychromatic418967fa.accept_11_2_9_4_1_310 13 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 169 (accept_3_3 11 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 169 (Polychromatic418967fa.accept_15_10_7_4_1_1222 10 97 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 169
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 169 (accept_3_3 8 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  169 (Polychromatic418967fa.accept_14_7_13_1_1_922 7 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 169 (Polychromatic418967fa.accept_20_6_17_9_1_7975 6 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 169 (accept_3_3 5 97 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 169 (Polychromatic418967fa.accept_19_4_2_17_1_3870 4 97 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 169
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 3 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 169 (accept_3_3 2 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  169 (Polychromatic418967fa.accept_17_1_12_16_1_2211 1 97 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 97 169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74
  96 169 (Eq.refl Bool.true) (allA_succ_of_accept 73 96 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 96 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 169
  (Polychromatic418967fa.accept_19_15_1_17_1_670 72 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 96 169 (accept_3_3 71 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  96 169 (Polychromatic418967fa.accept_15_10_6_4_1_1256 70 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 96 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 169 (accept_3_3 68 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 96 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 169
  (Polychromatic418967fa.accept_7_3_5_1_1_72 66 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 96 169 (accept_3_3 65 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  96 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 96 169 (Polychromatic418967fa.accept_10_3_6_9_1_779 63 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 169 (accept_3_3 62 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 169 (Polychromatic418967fa.accept_19_4_1_17_1_8064 61 96 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 169
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 96 169 (accept_3_3 59 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  96 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 96 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 169 (accept_3_3 56 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 96 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 169
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 54 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 96 169 (accept_3_3 53 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  96 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 96 169 (Polychromatic418967fa.accept_11_7_8_4_1_718 51 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 169 (accept_3_3 50 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 96 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 169
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 169 (accept_3_3 47 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  96 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 169 (accept_3_3 44 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 169 (Polychromatic418967fa.accept_10_3_6_9_1_779 43 96 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 169
  (Polychromatic418967fa.accept_19_4_1_17_1_8064 42 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 96 169 (accept_3_3 41 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  96 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 96 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 169 (accept_3_3 38 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 96 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 169
  (Polychromatic418967fa.accept_21_15_12_1_1_9491 36 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 169 (accept_3_3 35 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  96 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 169 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 169 (accept_3_3 32 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 96 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 169 (accept_3_3 29 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 169 (accept_3_3 26 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 96 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 169
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 169 (accept_3_3 23 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 169 (accept_3_3 20 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 96 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 169
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 169 (accept_3_3 17 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 169 (Polychromatic418967fa.accept_19_16_1_17_1_8065 16 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 169 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 169 (accept_3_3 14 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 96 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 169 (accept_3_3 11 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 169 (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 169 (accept_3_3 8 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 169 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 96 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 169
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 169 (accept_3_3 5 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  169 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 96 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 96 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 169 (accept_3_3 2 96 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 96 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 95 169 (Eq.refl
  Bool.true) (allA_of_3_1 75 95 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 94 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 94 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 94 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 94 169 (accept_3_3 74 94 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 94 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 94 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 72
  94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 169 (accept_3_3 71 94
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 169
  (Polychromatic418967fa.accept_18_16_4_7_1_2927 70 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 94 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 94 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 94 169 (accept_3_3 68 94 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 94 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 94 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 66
  94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 169 (accept_3_3 65 94
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 169 (Polychromatic418967fa.accept_9_1_4_7_1_7
  64 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 169 (accept_3_3 62 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 169 (accept_3_3 59 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 94 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 169 (accept_3_3 56 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 169 (accept_3_3 53 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 94 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 169 (accept_3_3 50 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 169 (Polychromatic418967fa.accept_18_13_4_7_1_4086 49 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 169 (accept_3_3 47 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 94 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 169 (accept_3_3 44 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 169 (accept_3_3 41 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 94 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 169 (accept_3_3 38 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 169 (Polychromatic418967fa.accept_16_4_14_9_1_4657 36 94 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 169 (accept_3_3 35 94 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 169 (Polychromatic418967fa.accept_18_16_4_7_1_2927 34 94
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 169 (accept_3_3 32 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 169 (accept_3_3 29 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 94 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 169 (accept_3_3 26 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 169 (accept_3_3 23 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 169 (Polychromatic418967fa.accept_26_22_16_13_1_9490 22 94 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 169 (accept_3_3 20 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 169 (accept_3_3 17 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 94 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 169 (accept_3_3 14 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 169 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 169 (accept_3_3 11 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 94 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 169 (accept_3_3 8 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 94 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 169 (accept_3_3 5 94 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 94 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 169 (accept_3_3 2 94 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 94
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 93 169 (Eq.refl
  Bool.true) (allA_succ_of_accept 76 93 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 169 (Polychromatic418967fa.accept_12_3_9_1_1_290
  75 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 169 (accept_3_3 74
  93 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 73 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 93 169 (Polychromatic418967fa.accept_26_20_15_13_1_9489 72 93 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 169 (accept_3_3 71 93 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 93 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 69
  93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 169 (accept_3_3 68 93
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 169
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 93 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 93 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 169 (accept_3_3 65 93 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 93 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 169 (Polychromatic418967fa.accept_12_3_9_1_1_290
  63 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 169 (accept_3_3 62
  93 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 93 169
  (Polychromatic418967fa.accept_15_1_3_4_1_1217 61 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 93 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 93 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 169 (accept_3_3 59 93 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 93 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 169
  (Polychromatic418967fa.accept_25_7_18_19_1_9488 57 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 169 (accept_3_3 56 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 169 (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 169 (accept_3_3 53 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 93 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 169 (accept_3_3 50 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 169 (accept_3_3 47 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 93 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 169 (accept_3_3 44 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 169 (Polychromatic418967fa.accept_11_10_5_4_1_711 43 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 169 (accept_3_3 41 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 169
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 169 (accept_3_3 38 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 169 (accept_3_3 35 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 93 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 169 (accept_3_3 32 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 169 (Polychromatic418967fa.accept_18_12_3_7_1_5373 30 93 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 169 (accept_3_3 29 93 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 169
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 169 (accept_3_3 26 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 169 (Polychromatic418967fa.accept_22_3_5_15_1_7860 25 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 169 (accept_3_3 23 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 93 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 169
  (Polychromatic418967fa.accept_11_10_5_4_1_711 21 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 169 (accept_3_3 20 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 169 (Polychromatic418967fa.accept_21_18_9_1_1_9467 18 93 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 169 (accept_3_3 17 93 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 169 (accept_3_3 14 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 169 (accept_3_3 11 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 93 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 169
  (Polychromatic418967fa.accept_17_9_8_16_1_2176 9 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 169 (accept_3_3 8 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  169 (Polychromatic418967fa.accept_15_7_3_4_1_574 7 93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 93 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 169 (accept_3_3 5 93 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  93 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 169 (accept_3_3 2 93 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 93
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 92 169 (Eq.refl
  Bool.true) (allA_of_3_1 78 92 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 91 169 (Eq.refl Bool.true)
  (allA_succ_of_gcd 78 91 169 13 6 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 91 169 (accept_3_3 77 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  91 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 91 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 75 91 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 169 (accept_3_3 74 91 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 169 (Polychromatic418967fa.accept_11_7_3_4_1_729 73 91 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 169
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 91 169 (accept_3_3 71 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  91 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 91 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 91 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 169 (accept_3_3 68 91 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 91 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 91 169 13 5 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 91 169 (Polychromatic418967fa.accept_14_8_7_1_1_1615 64 91 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 169 (Polychromatic418967fa.accept_15_3_1_4_1_1246 63 91 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 169 (accept_3_3 62 91 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 169
  (Polychromatic418967fa.accept_17_10_6_16_1_6862 61 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 91 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 91 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 169 (accept_3_3 59 91 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 91 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 91 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 57
  91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 169 (accept_3_3 56 91
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 169
  (Polychromatic418967fa.accept_10_5_1_9_1_791 55 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 91 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 91 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 169 (accept_3_3 53 91 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 91 169 13 4 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 91 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 91 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 169 (accept_3_3 50 91 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 91 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 169
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 169 (accept_3_3 47 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 169 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 91 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 169 (accept_3_3 44 91 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 169 (Polychromatic418967fa.accept_17_9_6_16_1_3280 43 91 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 169 (accept_3_3 41 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 91 169 13 3 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 91 169 (accept_3_3 38 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 91 169 (Polychromatic418967fa.accept_16_5_11_9_1_861 37 91 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 169 (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 91 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 169 (accept_3_3 35 91 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34
  91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 169
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 169 (accept_3_3 32 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 169 (accept_3_3 29 91 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 169 (Polychromatic418967fa.accept_10_8_1_9_1_413 28 91 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 169
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 91 169 13 2 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 91 169 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 91 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 91 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 169 (accept_3_3 23 91 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22
  91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 169
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 169 (accept_3_3 20 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 169 (Polychromatic418967fa.accept_21_19_7_1_1_3329 19 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 169 (accept_3_3 17 91 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 169 (Polychromatic418967fa.accept_18_16_1_7_1_4083 16 91 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 169
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 169 (accept_3_3 14 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 91
  169 13 1 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12
  91 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 91 169 (accept_3_3 11 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 91 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 169 (Polychromatic418967fa.accept_17_9_6_16_1_3280 9 91 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 169 (accept_3_3 8 91 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 169 (Polychromatic418967fa.accept_11_7_3_4_1_729 7
  91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 169 (accept_3_3 5 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  169 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 91 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 91 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 169 (accept_3_3 2 91 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 169 (Polychromatic418967fa.accept_19_1_15_17_1_701 1 91 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 90 169 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 90 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 169 (Polychromatic418967fa.accept_19_2_14_17_1_700
  78 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 90 169 (accept_3_3 77
  90 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 90 169
  (Polychromatic418967fa.accept_20_16_10_9_1_9431 76 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 90 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 90 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 90 169 (accept_3_3 74 90 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 90 169 (Polychromatic418967fa.accept_19_16_14_17_1_3863 73 90 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 169
  (Polychromatic418967fa.accept_7_2_6_1_1_73 72 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 90 169 (accept_3_3 71 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  90 169 (Polychromatic418967fa.accept_17_2_5_16_1_1264 70 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 90 169 (Polychromatic418967fa.accept_17_1_5_16_1_5589 69 90 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 90 169 (accept_3_3 68 90 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 90 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 169
  (Polychromatic418967fa.accept_19_9_14_17_1_2613 66 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 90 169 (accept_3_3 65 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  90 169 (Polychromatic418967fa.accept_11_9_2_4_1_707 64 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 90 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 169 (accept_3_3 62 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 90 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 169
  (Polychromatic418967fa.accept_19_3_14_17_1_6603 60 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 90 169 (accept_3_3 59 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  90 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 90 169 (Polychromatic418967fa.accept_20_17_10_9_1_6409 57 90 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 169 (accept_3_3 56 90 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 90 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 169
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 90 169 (accept_3_3 53 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  90 169 (Polychromatic418967fa.accept_17_1_5_16_1_5589 52 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 90 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 90 169 (accept_3_3 50 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 169 (Polychromatic418967fa.accept_14_7_6_1_1_1656 49 90 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 169
  (Polychromatic418967fa.accept_25_23_15_19_1_9487 48 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 90 169 (accept_3_3 47 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 90 169 (Polychromatic418967fa.accept_20_6_10_9_1_3486 46 90 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 90 169 (Polychromatic418967fa.accept_17_11_5_16_1_5600 45 90
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 169 (accept_3_3 44 90 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 43
  90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 169
  (Polychromatic418967fa.accept_11_9_2_4_1_707 42 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 90 169 (accept_3_3 41 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  90 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 90 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 169 (accept_3_3 38 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 90 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 169
  (Polychromatic418967fa.accept_17_2_5_16_1_1264 36 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 90 169 (accept_3_3 35 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  90 169 (Polychromatic418967fa.accept_19_15_14_17_1_9486 34 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 90 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 169 (accept_3_3 32 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 90 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 169
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 90 169 (accept_3_3 29 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  90 169 (Polychromatic418967fa.accept_11_6_2_4_1_1703 28 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 90 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 169 (accept_3_3 26 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 169 (Polychromatic418967fa.accept_20_5_10_9_1_9485 25 90 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 169
  (Polychromatic418967fa.accept_19_5_14_17_1_6550 24 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 90 169 (accept_3_3 23 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  90 169 (Polychromatic418967fa.accept_19_3_14_17_1_6603 22 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 90 169 (Polychromatic418967fa.accept_14_7_6_1_1_1656 21 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 169 (accept_3_3 20 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 169
  (Polychromatic418967fa.accept_17_1_5_16_1_5589 18 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 90 169 (accept_3_3 17 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  90 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 90 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 169 (accept_3_3 14 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 169 (Polychromatic418967fa.accept_20_13_10_9_1_5030 13 90 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 169
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 90 169 (accept_3_3 11 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  90 169 (Polychromatic418967fa.accept_23_10_21_8_1_9484 10 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 90 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 169 (accept_3_3 8 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 169
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 90 169 (accept_3_3 5 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90
  169 (Polychromatic418967fa.accept_17_4_5_16_1_3240 4 90 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 90 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 169 (accept_3_3 2 90 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 169 (Polychromatic418967fa.accept_16_1_10_9_1_4645 1 90 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 89 169 (Eq.refl
  Bool.true) (allA_of_3_1 81 89 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 88 169 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 88 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 88 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 88 169 (accept_3_3 80 88 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 88 169 (Polychromatic418967fa.accept_16_15_8_9_1_2563 79 88 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 88 169
  (Polychromatic418967fa.accept_19_2_12_17_1_5197 78 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 88 169 (accept_3_3 77 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  88 169 (Polychromatic418967fa.accept_16_12_8_9_1_2583 76 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 88 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 88 169 (accept_3_3 74 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 88 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 88 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 88 169
  (Polychromatic418967fa.accept_17_4_3_16_1_9483 72 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 88 169 (accept_3_3 71 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  88 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 88 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 88 169 (accept_3_3 68 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 88 169 (Polychromatic418967fa.accept_10_7_8_9_1_785 67 88 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 88 169
  (Polychromatic418967fa.accept_7_3_4_1_1_71 66 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 88 169 (accept_3_3 65 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  88 169 (Polychromatic418967fa.accept_10_4_8_9_1_784 64 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 88 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 169 (accept_3_3 62 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 88 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 88 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 169
  (Polychromatic418967fa.accept_16_12_8_9_1_2583 60 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 88 169 (accept_3_3 59 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  88 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 88 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 169 (accept_3_3 56 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 88 169 (Polychromatic418967fa.accept_15_10_13_4_1_1210 55 88 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 88 169
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 88 169 (accept_3_3 53 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  88 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 88 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 169 (accept_3_3 50 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 88 169 (Polychromatic418967fa.accept_16_1_8_9_1_3462 49 88 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 169
  (Polychromatic418967fa.accept_19_10_12_17_1_1506 48 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 88 169 (accept_3_3 47 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 88 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 88 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 169 (accept_3_3 44 88 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 169
  (Polychromatic418967fa.accept_19_5_12_17_1_8089 43 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 88 169 (Polychromatic418967fa.accept_25_17_13_19_1_9482 42 88 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 169 (accept_3_3 41 88 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 88 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 39
  88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 169 (accept_3_3 38 88
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 169
  (Polychromatic418967fa.accept_10_7_8_9_1_785 37 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 88 169 (Polychromatic418967fa.accept_15_6_13_4_1_2040 36 88 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 169 (accept_3_3 35 88 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 88 169 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 88 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 33
  88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 169 (accept_3_3 32 88
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 169 (Polychromatic418967fa.accept_7_3_4_1_1_71
  31 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 169
  (Polychromatic418967fa.accept_17_13_3_16_1_5599 30 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 169 (accept_3_3 29 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 169 (Polychromatic418967fa.accept_16_12_8_9_1_2583 28 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 169 (accept_3_3 26 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 169 (Polychromatic418967fa.accept_14_11_4_1_1_4255 25 88 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 169
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 169 (accept_3_3 23 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 169 (accept_3_3 20 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 88 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 169
  (Polychromatic418967fa.accept_19_18_12_17_1_8026 18 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 88 169 (accept_3_3 17 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 88 169 (Polychromatic418967fa.accept_26_16_10_13_1_9481 16 88 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 169 (accept_3_3 14 88 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 169
  (Polychromatic418967fa.accept_17_13_3_16_1_5599 13 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 88 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 88 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 169 (accept_3_3 11 88 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 88 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 169 (accept_3_3 8 88 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 169 (Polychromatic418967fa.accept_10_7_8_9_1_785 7
  88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 169
  (Polychromatic418967fa.accept_15_6_13_4_1_2040 6 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 169 (accept_3_3 5 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  169 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 88 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 88 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 169 (accept_3_3 2 88 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 88 169 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 88 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 87 169 (Eq.refl
  Bool.true) (allA_succ_of_accept 82 87 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 81
  87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 87 169 (accept_3_3 80 87
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 169 (Polychromatic418967fa.accept_7_2_3_1_1_10
  79 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 87 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 87 169 (accept_3_3 77 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  87 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 87 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 169 (accept_3_3 74 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 87 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 87 169
  (Polychromatic418967fa.accept_7_2_3_1_1_10 72 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 87 169 (accept_3_3 71 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  87 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 87 169 (Polychromatic418967fa.accept_12_9_3_1_1_303 69 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 169 (accept_3_3 68 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 87 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 87 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 87 169 (accept_3_3 65 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  87 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 87 169 (Polychromatic418967fa.accept_19_6_11_17_1_2611 63 87 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 169 (accept_3_3 62 87 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 87 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 87 169
  (Polychromatic418967fa.accept_7_4_3_1_1_87 60 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 87 169 (accept_3_3 59 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  87 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 87 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 169 (accept_3_3 56 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 87 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 87 169 (accept_3_3 53 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  87 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 87 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 169 (accept_3_3 50 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 87 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 87 169 (accept_3_3 47 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  87 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 87 169 (Polychromatic418967fa.accept_12_9_3_1_1_303 45 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 169 (accept_3_3 44 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 169 (Polychromatic418967fa.accept_19_5_11_17_1_6536 43 87 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 87 169 (accept_3_3 41 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  87 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 87 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 169 (accept_3_3 38 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 87 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 169
  (Polychromatic418967fa.accept_20_16_7_9_1_9462 36 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 87 169 (accept_3_3 35 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  87 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 87 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 169 (accept_3_3 32 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 87 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 87 169 (accept_3_3 29 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  87 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 87 169 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 87 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 169 (accept_3_3 26 87 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 87 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 169
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 24 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 87 169 (accept_3_3 23 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  87 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 87 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 169 (accept_3_3 20 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 87 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 87 169 (accept_3_3 17 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  87 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 87 169 (Polychromatic418967fa.accept_21_15_3_1_1_6338 15 87 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 169 (accept_3_3 14 87 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 87 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 169
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 87 169 (accept_3_3 11 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  87 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 87 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 169 (accept_3_3 8 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 169 (Polychromatic418967fa.accept_15_7_12_4_1_1236 7 87 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 169 (accept_3_3 5 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87
  169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 87 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 87 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 169 (accept_3_3 2 87 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 87 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 87 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 86 169 (Eq.refl
  Bool.true) (allA_of_3_1 84 86 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 169 (allA_succ_of_accept 84
  85 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 85 169 (accept_3_3 83 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 85 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 85 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 169 (Polychromatic418967fa.accept_10_1_5_9_1_157 81 85 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 169 (accept_3_3 80 85 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 169
  (Polychromatic418967fa.accept_23_10_16_8_1_9480 79 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 78 85 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 169 (accept_3_3 77 85 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 76 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 85 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 75
  85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 169 (accept_3_3 74 85
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 169 (Polychromatic418967fa.accept_9_1_4_7_1_7
  73 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 169
  (Polychromatic418967fa.accept_22_6_19_15_1_9479 72 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 169 (accept_3_3 71 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 169 (Polychromatic418967fa.accept_19_13_9_17_1_8070 70 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 169 (accept_3_3 68 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 169 (Polychromatic418967fa.accept_11_1_8_4_1_717 67 85 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 169 (accept_3_3 65 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 169 (Polychromatic418967fa.accept_19_6_9_17_1_5214 63 85 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 169 (accept_3_3 62 85 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 169 (Polychromatic418967fa.accept_10_1_5_9_1_157 61 85 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 169
  (Polychromatic418967fa.accept_8_4_5_1_1_299 60 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 169 (accept_3_3 59 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 169 (Polychromatic418967fa.accept_15_13_10_4_1_1232 58 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 169 (accept_3_3 56 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 85 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 169
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 169 (accept_3_3 53 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 52 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 169 (accept_3_3 50 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 169 (Polychromatic418967fa.accept_16_1_5_9_1_1649 49 85 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 169 (accept_3_3 47 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 169 (Polychromatic418967fa.accept_11_1_8_4_1_717 45 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 169 (accept_3_3 44 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 169 (Polychromatic418967fa.accept_15_13_10_4_1_1232 43 85 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 169 (accept_3_3 41 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 169 (Polychromatic418967fa.accept_11_7_8_4_1_718 40 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 169 (accept_3_3 38 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 85 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 169
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 169 (accept_3_3 35 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 169 (Polychromatic418967fa.accept_10_4_5_9_1_1231 34 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 169 (accept_3_3 32 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 169 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 85 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 169 (accept_3_3 29 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 169 (Polychromatic418967fa.accept_16_11_5_9_1_1617 27 85 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 169 (accept_3_3 26 85 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 169 (Polychromatic418967fa.accept_19_6_9_17_1_5214 25 85
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 169 (accept_3_3 23 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 169 (Polychromatic418967fa.accept_15_7_10_4_1_151 22 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 169 (accept_3_3 20 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 85 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 169
  (Polychromatic418967fa.accept_11_7_8_4_1_718 18 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 169 (accept_3_3 17 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 169 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 169 (accept_3_3 14 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 169 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 85 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 169
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 169 (accept_3_3 11 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 169 (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 169 (accept_3_3 8 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 169 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 85 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 169 (accept_3_3 5 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  169 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 85 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 85 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 169 (accept_3_3 2 85 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 85 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 169
  (allA_succ_of_accept 83 84 169 (accept_3_3 83 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  84 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 84 169 (Polychromatic418967fa.accept_15_6_9_4_1_1227 81 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 84 169 (accept_3_3 80 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 169 (Polychromatic418967fa.accept_19_3_8_17_1_5213 79 84 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 78 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 84 169 (accept_3_3 77 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  84 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 84 169 (Polychromatic418967fa.accept_10_5_4_9_1_420 75 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 84 169 (accept_3_3 74 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 84 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 169
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 72 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 84 169 (accept_3_3 71 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  84 169 (Polychromatic418967fa.accept_15_10_9_4_1_2924 70 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 84 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 84 169 (accept_3_3 68 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 67 84 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 169
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 66 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 84 169 (accept_3_3 65 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  84 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 84 169 (Polychromatic418967fa.accept_10_3_4_9_1_15 63 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 84 169 (accept_3_3 62 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 84 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 84 169 (accept_3_3 59 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  84 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 84 169 (Polychromatic418967fa.accept_15_12_9_4_1_3898 57 84 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 84 169 (accept_3_3 56 84 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 84 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 169
  (Polychromatic418967fa.accept_19_16_8_17_1_5148 54 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 84 169 (accept_3_3 53 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  84 169 (Polychromatic418967fa.accept_11_8_7_4_1_3011 52 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 84 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 169 (accept_3_3 50 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 84 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 169
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 169 (accept_3_3 47 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  84 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 169 (accept_3_3 44 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 169 (Polychromatic418967fa.accept_10_3_4_9_1_15 43 84 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 84 169 (accept_3_3 41 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  84 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 84 169 (Polychromatic418967fa.accept_18_3_12_7_1_6728 39 84 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 169 (accept_3_3 38 84 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 84 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 169
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 84 169 (accept_3_3 35 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  84 169 (Polychromatic418967fa.accept_19_15_8_17_1_9429 34 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 84 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 169 (accept_3_3 32 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 84 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 169
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 84 169 (accept_3_3 29 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  84 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 84 169 (Polychromatic418967fa.accept_15_12_9_4_1_3898 27 84 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 169 (accept_3_3 26 84 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 169 (Polychromatic418967fa.accept_10_5_4_9_1_420 25 84 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 84 169 (accept_3_3 23 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  84 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 84 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 169 (accept_3_3 20 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 84 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 169
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 169 (accept_3_3 17 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 169 (Polychromatic418967fa.accept_19_16_8_17_1_5148 16 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 169 (accept_3_3 14 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 84 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 169
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 169 (accept_3_3 11 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 169 (Polychromatic418967fa.accept_19_9_8_17_1_8053 9 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 169 (accept_3_3 8 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 169 (Polychromatic418967fa.accept_23_7_15_8_1_9478 7 84 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 169 (accept_3_3 5 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  169 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 84 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 84 169 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 84 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 169 (accept_3_3 2 84 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 84 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 84 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 169 (allA_of_3_1
  83 83 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 169 (allA_succ_of_accept 81 82 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 82 169 (accept_3_3 80 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  82 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 82 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 78 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 169 (accept_3_3 77 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 76 82 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 82 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 82 169 (accept_3_3 74 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  82 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 82 169 (Polychromatic418967fa.accept_15_12_7_4_1_2921 72 82 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 169 (accept_3_3 71 82 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 169 (Polychromatic418967fa.accept_15_10_7_4_1_1222 70 82
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 82 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 82 169 (accept_3_3 68 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  82 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 82 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 169 (accept_3_3 65 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 82 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 82 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 82 169 (accept_3_3 62 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  82 169 (Polychromatic418967fa.accept_10_1_2_9_1_152 61 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 82 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 169 (accept_3_3 59 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 82 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 82 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 82 169 (accept_3_3 56 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  82 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 82 169 (Polychromatic418967fa.accept_11_10_5_4_1_711 54 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 169 (accept_3_3 53 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 82 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 82 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 82 169 (accept_3_3 50 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  82 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 82 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 169 (accept_3_3 47 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 82 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 82 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 82 169 (accept_3_3 44 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  82 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 82 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 169 (accept_3_3 41 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 82 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 82 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 82 169 (accept_3_3 38 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  82 169 (Polychromatic418967fa.accept_10_7_2_9_1_775 37 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 82 169 (Polychromatic418967fa.accept_17_2_14_16_1_2187 36 82 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 169 (accept_3_3 35 82 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 82 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 82 169 (accept_3_3 32 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  82 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 82 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 169 (accept_3_3 29 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 82 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 82 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 82 169 (accept_3_3 26 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  82 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 82 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 169 (accept_3_3 23 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 82 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 82 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 82 169 (accept_3_3 20 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  82 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 82 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 169 (accept_3_3 17 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 82 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 169 (accept_3_3 14 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  82 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 82 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 169 (accept_3_3 11 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 82 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 82 169 (accept_3_3 8 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82
  169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 82 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 82 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 169 (accept_3_3 5 82 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 82 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 82 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 169 (accept_3_3 2 82 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 169 (Polychromatic418967fa.accept_10_1_2_9_1_152 1
  82 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 169
  (allA_succ_of_accept 80 81 169 (accept_3_3 80 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 169 (Polychromatic418967fa.accept_19_3_5_17_1_9438 79 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 169 (Polychromatic418967fa.accept_10_8_1_9_1_413 78 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 169 (accept_3_3 77 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 81 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 169
  (Polychromatic418967fa.accept_7_5_4_1_1_412 75 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 169 (accept_3_3 74 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 169 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 169 (accept_3_3 71 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 81 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 169
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 69 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 169 (accept_3_3 68 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 169 (Polychromatic418967fa.accept_21_4_18_1_1_6333 67 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 169 (accept_3_3 65 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 81 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 169
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 169 (accept_3_3 62 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 169 (Polychromatic418967fa.accept_14_4_11_1_1_940 60 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 169 (accept_3_3 59 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 81 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 169
  (Polychromatic418967fa.accept_18_3_9_7_1_1839 57 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 169 (accept_3_3 56 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 169 (Polychromatic418967fa.accept_10_5_1_9_1_791 55 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 169 (accept_3_3 53 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 169
  (Polychromatic418967fa.accept_12_3_9_1_1_290 51 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 169 (accept_3_3 50 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 169 (Polychromatic418967fa.accept_19_11_5_17_1_2620 49 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 169 (Polychromatic418967fa.accept_10_8_1_9_1_413 48 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 169 (accept_3_3 47 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 81 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 169
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 169 (accept_3_3 44 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 169 (Polychromatic418967fa.accept_15_13_6_4_1_1221 43 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 169 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 169 (accept_3_3 41 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 169
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 169 (accept_3_3 38 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 169 (Polychromatic418967fa.accept_16_5_1_9_1_4621 37 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 169 (Polychromatic418967fa.accept_21_15_18_1_1_6300 36 81 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 169 (accept_3_3 35 81 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 81 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 169
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 169 (accept_3_3 32 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 169 (Polychromatic418967fa.accept_19_11_5_17_1_2620 30 81 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 169 (accept_3_3 29 81 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 169
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 169 (accept_3_3 26 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 169 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 169 (accept_3_3 23 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 81 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 169
  (Polychromatic418967fa.accept_16_5_1_9_1_4621 21 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 169 (accept_3_3 20 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 169 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 169 (accept_3_3 17 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 169
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 169 (accept_3_3 14 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 169 (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 169 (accept_3_3 11 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 81 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 169
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 169 (accept_3_3 8 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  169 (Polychromatic418967fa.accept_19_7_5_17_1_3849 7 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 169 (Polychromatic418967fa.accept_18_6_9_7_1_2905 6 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 169 (accept_3_3 5 81 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 169
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 169 (accept_3_3 2 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  169 (Polychromatic418967fa.accept_23_1_12_8_1_9477 1 81 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 169 (allA_of_3_1 80 80 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 169
  (allA_succ_of_accept 78 79 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 79 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 169 (accept_3_3 77 79 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 76 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 169 (Polychromatic418967fa.accept_11_9_2_4_1_707
  75 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 169 (accept_3_3 74
  79 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 73 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 79 169 (Polychromatic418967fa.accept_11_6_2_4_1_1703 72 79 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 169 (accept_3_3 71 79 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 79 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 69
  79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 169 (accept_3_3 68 79
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 169
  (Polychromatic418967fa.accept_23_21_10_8_1_9476 67 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 79 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 79 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 169 (accept_3_3 65 79 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 79 169 (Polychromatic418967fa.accept_11_9_2_4_1_707 64 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 169
  (Polychromatic418967fa.accept_17_12_11_16_1_6903 63 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 79 169 (accept_3_3 62 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 79 169 (Polychromatic418967fa.accept_11_6_2_4_1_1703 61 79 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 169 (Polychromatic418967fa.accept_25_10_4_19_1_9475 60 79
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 169 (accept_3_3 59 79 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 58
  79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 169
  (Polychromatic418967fa.accept_21_15_16_1_1_9474 57 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 169 (accept_3_3 56 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 169 (accept_3_3 53 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 79 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 169
  (Polychromatic418967fa.accept_22_7_13_15_1_9473 51 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 169 (accept_3_3 50 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 169 (Polychromatic418967fa.accept_17_15_11_16_1_3263 49 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 169 (accept_3_3 47 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 169 (accept_3_3 44 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 169 (Polychromatic418967fa.accept_19_5_3_17_1_6557 43 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 169 (accept_3_3 41 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 169 (Polychromatic418967fa.accept_16_8_15_9_1_4676 40 79 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 169
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 169 (accept_3_3 38 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 169 (Polychromatic418967fa.accept_24_13_7_1_1_7774 37 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 169 (Polychromatic418967fa.accept_14_8_9_1_1_3313 36 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 169 (accept_3_3 35 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 169
  (Polychromatic418967fa.accept_19_14_3_17_1_6558 33 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 169 (accept_3_3 32 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 169 (accept_3_3 29 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 169 (Polychromatic418967fa.accept_11_6_2_4_1_1703 28 79 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 169
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 169 (accept_3_3 26 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 169 (Polychromatic418967fa.accept_19_6_3_17_1_9472 25 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 169 (accept_3_3 23 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 169
  (Polychromatic418967fa.accept_19_2_3_17_1_5146 21 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 169 (accept_3_3 20 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 169 (Polychromatic418967fa.accept_21_19_16_1_1_2053 19 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 169 (accept_3_3 17 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 169 (Polychromatic418967fa.accept_19_16_3_17_1_6575 16 79 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 169
  (Polychromatic418967fa.accept_17_15_11_16_1_3263 15 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 79 169 (accept_3_3 14 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 79 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 79 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 169 (Polychromatic418967fa.accept_17_12_11_16_1_6903 12 79
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 169 (accept_3_3 11 79 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10
  79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 169
  (Polychromatic418967fa.accept_11_9_2_4_1_707 9 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 169 (accept_3_3 8 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  169 (Polychromatic418967fa.accept_21_7_16_1_1_6298 7 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 169 (accept_3_3 5 79 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 169 (Polychromatic418967fa.accept_20_4_19_9_1_7961 4 79 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 169 (accept_3_3 2 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  169 (Polychromatic418967fa.accept_19_1_3_17_1_1502 1 79 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 79 169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  78 169 (allA_succ_of_accept 77 78 169 (accept_3_3 77 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 78 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 78 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 78 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 78 169 (accept_3_3 74 78 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 73
  78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 169
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 72 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 78 169 (accept_3_3 71 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  78 169 (Polychromatic418967fa.accept_21_7_15_1_1_6330 70 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 78 169 (Polychromatic418967fa.accept_16_5_14_9_1_2572 69 78 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 78 169 (accept_3_3 68 78 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 78 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 78 169 13 5 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 78 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 78 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 78 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 169 (accept_3_3 62 78 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 169 (Polychromatic418967fa.accept_10_1_8_9_1_787
  61 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 169
  (Polychromatic418967fa.accept_17_9_10_16_1_3217 60 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 78 169 (accept_3_3 59 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  78 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 78 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 78 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 169 (accept_3_3 56 78 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 169
  (Polychromatic418967fa.accept_10_4_8_9_1_784 54 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 78 169 (accept_3_3 53 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78
  169 13 4 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  78 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 169 (accept_3_3 50 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 78 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 78 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 78 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 169 (accept_3_3 47 78 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 78 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 46
  78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 78 169
  (Polychromatic418967fa.accept_18_9_6_7_1_6719 45 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 78 169 (accept_3_3 44 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  78 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 78 169 (Polychromatic418967fa.accept_19_4_2_17_1_3870 42 78 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 169 (accept_3_3 41 78 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 78 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 78 169 13 3 6 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 78 169 (accept_3_3 38 78 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 37
  78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 169
  (Polychromatic418967fa.accept_16_4_14_9_1_4657 36 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 169 (accept_3_3 35 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 169 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 169 (Polychromatic418967fa.accept_19_14_2_17_1_678 33 78 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 169 (accept_3_3 32 78 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 169 (accept_3_3 29 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 169 13 2 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 169 (Polychromatic418967fa.accept_22_3_12_15_1_9471
  25 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 169
  (Polychromatic418967fa.accept_10_4_8_9_1_784 24 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 169 (accept_3_3 23 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 78 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 169 (accept_3_3 20 78 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 169
  (Polychromatic418967fa.accept_21_18_15_1_1_9470 18 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 169 (accept_3_3 17 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 169 (Polychromatic418967fa.accept_14_2_8_1_1_1647 16 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 169 (accept_3_3 14 78 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 13 78 169 13 1 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 12 78 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 78 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 169 (accept_3_3 11 78 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 78 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 78 169
  (Polychromatic418967fa.accept_14_9_8_1_1_2381 9 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 169 (accept_3_3 8 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78
  169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 78 169 (Polychromatic418967fa.accept_17_6_10_16_1_9453 6 78 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 169 (accept_3_3 5 78 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 78 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 78 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 169 (accept_3_3 2 78 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  78 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 169 (allA_of_3_1 77 77
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 169 (allA_succ_of_accept 75 76 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 76 169 (accept_3_3 74 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  76 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 76 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 169 (accept_3_3 71 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 76 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 76 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 76 169 (accept_3_3 68 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  76 169 (Polychromatic418967fa.accept_16_3_12_9_1_8250 67 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 76 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 169 (accept_3_3 65 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 76 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 169 (accept_3_3 62 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 169 (accept_3_3 59 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 76 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 76 169 (accept_3_3 56 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  76 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 76 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 169 (accept_3_3 53 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 169 (Polychromatic418967fa.accept_16_4_12_9_1_2567 52 76 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 169 (accept_3_3 50 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 169 (Polychromatic418967fa.accept_11_5_10_4_1_1157 49 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 169 (accept_3_3 47 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 76 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 169 (accept_3_3 44 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 169 (Polychromatic418967fa.accept_10_3_6_9_1_779 43 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 169 (accept_3_3 41 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 76 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 76 169 (accept_3_3 38 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  76 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 76 169 (Polychromatic418967fa.accept_16_4_12_9_1_2567 36 76 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 169 (accept_3_3 35 76 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 76
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 169 (accept_3_3 32 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 169 (Polychromatic418967fa.accept_17_14_8_16_1_6863 31 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 169 (accept_3_3 29 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 76 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 169 (accept_3_3 26 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 169 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 169 (accept_3_3 23 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 76 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 169 (accept_3_3 20 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  76 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 76 169 (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 169 (accept_3_3 17 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 76 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 169 (accept_3_3 14 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 169 (accept_3_3 11 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 76 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 169 (accept_3_3 8 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  169 (Polychromatic418967fa.accept_14_7_6_1_1_1656 7 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 76 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 169 (accept_3_3 5 76 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 76 169 (Polychromatic418967fa.accept_16_4_12_9_1_2567 4 76 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 76 169 (accept_3_3 2 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76
  169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 76 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 169
  (allA_succ_of_accept 74 75 169 (accept_3_3 74 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  75 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 75 169 (Polychromatic418967fa.accept_21_9_12_1_1_7926 72 75 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 169 (accept_3_3 71 75 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 75 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 169
  (Polychromatic418967fa.accept_7_6_5_1_1_416 69 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 75 169 (accept_3_3 68 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  75 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 75 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 169 (accept_3_3 65 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 75 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 169
  (Polychromatic418967fa.accept_18_9_3_7_1_9449 63 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 75 169 (accept_3_3 62 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  75 169 (Polychromatic418967fa.accept_10_1_5_9_1_157 61 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 75 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 169 (accept_3_3 59 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 169
  (Polychromatic418967fa.accept_11_2_9_4_1_310 57 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 75 169 (accept_3_3 56 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  75 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 75 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 169 (accept_3_3 53 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 75 169 (accept_3_3 50 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  75 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 75 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 169 (accept_3_3 47 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 169
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 75 169 (accept_3_3 44 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  75 169 (Polychromatic418967fa.accept_19_5_18_17_1_8017 43 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 75 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 169 (accept_3_3 41 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 169
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 169 (accept_3_3 38 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  75 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 169 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 169 (accept_3_3 35 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 75 169 (accept_3_3 32 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  75 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 75 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 169 (accept_3_3 29 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 169
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 75 169 (accept_3_3 26 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  75 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 75 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 169 (accept_3_3 23 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 169
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 75 169 (accept_3_3 20 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  75 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 75 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 169 (accept_3_3 17 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 169 (accept_3_3 14 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  75 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 169 (Polychromatic418967fa.accept_18_12_3_7_1_5373 12 75 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 169 (accept_3_3 11 75 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 169
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 169 (accept_3_3 8 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75
  169 (Polychromatic418967fa.accept_19_7_18_17_1_663 7 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 75 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 169 (accept_3_3 5 75 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 169
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 75 169 (accept_3_3 2 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75
  169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 75 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 75 169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 169
  (allA_of_3_1 74 74 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 169 (allA_succ_of_accept 72 73 169
  (Polychromatic418967fa.accept_7_2_3_1_1_10 72 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 169 (accept_3_3 71 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 169 (Polychromatic418967fa.accept_15_10_13_4_1_1210 70 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 169 (accept_3_3 68 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 73 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 169
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 169 (accept_3_3 65 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 169 (Polychromatic418967fa.accept_10_4_3_9_1_1262 64 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 169 (Polychromatic418967fa.accept_11_8_7_4_1_3011 63 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 169 (accept_3_3 62 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 73 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 169
  (Polychromatic418967fa.accept_7_4_3_1_1_87 60 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 169 (accept_3_3 59 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 169 (accept_3_3 56 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 169 (Polychromatic418967fa.accept_15_10_13_4_1_1210 55 73 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 169
  (Polychromatic418967fa.accept_7_5_3_1_1_424 54 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 169 (accept_3_3 53 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 169 (Polychromatic418967fa.accept_11_8_7_4_1_3011 52 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 169 (accept_3_3 50 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 73 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 169
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 169 (accept_3_3 47 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 169 (Polychromatic418967fa.accept_17_11_5_16_1_5600 45 73 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 169 (accept_3_3 44 73 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 169 (Polychromatic418967fa.accept_27_16_19_7_1_9469 43 73
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 169
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 169 (accept_3_3 41 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 169 (accept_3_3 38 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 73 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 169
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 169 (accept_3_3 35 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 169 (Polychromatic418967fa.accept_10_4_3_9_1_1262 34 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 169 (accept_3_3 32 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 73 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 169
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 169 (accept_3_3 29 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 169 (Polychromatic418967fa.accept_17_11_5_16_1_5600 28 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 169 (Polychromatic418967fa.accept_19_8_16_17_1_6552 27 73 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 169 (accept_3_3 26 73 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 73 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 169
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 169 (accept_3_3 23 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 169 (accept_3_3 20 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 73 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 169
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 169 (accept_3_3 17 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 169 (accept_3_3 14 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 73 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 169
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 169 (accept_3_3 11 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 169 (Polychromatic418967fa.accept_15_10_13_4_1_1210 10 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 169 (accept_3_3 8 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 169 (Polychromatic418967fa.accept_19_7_16_17_1_6567 7 73 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 169
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 169 (accept_3_3 5 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  169 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 73 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 73 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 169 (accept_3_3 2 73 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 169 (Polychromatic418967fa.accept_17_1_5_16_1_5589 1 73 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 169 (allA_succ_of_accept 71
  72 169 (accept_3_3 71 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 169
  (Polychromatic418967fa.accept_19_13_15_17_1_5199 70 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 72 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 72 169 (accept_3_3 68 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 169 (Polychromatic418967fa.accept_10_7_2_9_1_775 67 72 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 66 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 72 169 (accept_3_3 65 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  72 169 (Polychromatic418967fa.accept_14_8_2_1_1_1652 64 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 72 169 (Polychromatic418967fa.accept_16_15_8_9_1_2563 63 72 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 72 169 (accept_3_3 62 72 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 169 (Polychromatic418967fa.accept_10_1_2_9_1_152 61 72 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 169
  (Polychromatic418967fa.accept_16_12_8_9_1_2583 60 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 72 169 (accept_3_3 59 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  72 169 (Polychromatic418967fa.accept_19_1_15_17_1_701 58 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 72 169 (Polychromatic418967fa.accept_10_7_2_9_1_775 57 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 169 (accept_3_3 56 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 72 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 169
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 54 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 72 169 (accept_3_3 53 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  72 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 72 169 (Polychromatic418967fa.accept_10_1_2_9_1_152 51 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 169 (accept_3_3 50 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 169 (Polychromatic418967fa.accept_16_1_8_9_1_3462 49 72 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 169
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 72 169 (accept_3_3 47 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  72 169 (Polychromatic418967fa.accept_11_2_6_4_1_3028 46 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 72 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 169 (accept_3_3 44 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 169 (Polychromatic418967fa.accept_19_5_15_17_1_9432 43 72 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 169
  (Polychromatic418967fa.accept_20_2_12_9_1_6435 42 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 72 169 (accept_3_3 41 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  72 169 (Polychromatic418967fa.accept_19_2_15_17_1_2614 40 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 72 169 (Polychromatic418967fa.accept_15_9_12_4_1_2023 39 72 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 169 (accept_3_3 38 72 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 169 (Polychromatic418967fa.accept_10_7_2_9_1_775 37 72 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 169
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 169 (accept_3_3 35 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  72 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 169 (Polychromatic418967fa.accept_16_1_8_9_1_3462 33 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 169 (accept_3_3 32 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 72 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 169
  (Polychromatic418967fa.accept_22_8_6_15_1_7862 30 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 169 (accept_3_3 29 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 169 (Polychromatic418967fa.accept_16_12_8_9_1_2583 28 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 169 (accept_3_3 26 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 169 (Polychromatic418967fa.accept_27_25_18_7_1_9468 25 72 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 169 (accept_3_3 23 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 169 (Polychromatic418967fa.accept_14_8_2_1_1_1652 22 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 169 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 169 (accept_3_3 20 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 169 (Polychromatic418967fa.accept_20_19_12_9_1_4996 19 72 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 169
  (Polychromatic418967fa.accept_21_18_9_1_1_9467 18 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 169 (accept_3_3 17 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  72 169 (Polychromatic418967fa.accept_15_1_12_4_1_2022 16 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 169 (Polychromatic418967fa.accept_16_15_8_9_1_2563 15 72 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 169 (accept_3_3 14 72 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 72 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 169
  (Polychromatic418967fa.accept_16_12_8_9_1_2583 12 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 169 (accept_3_3 11 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 169 (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 169 (accept_3_3 8 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 169 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 72 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 169
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 169 (accept_3_3 5 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  169 (Polychromatic418967fa.accept_16_4_8_9_1_4639 4 72 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 72 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 169 (accept_3_3 2 72 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 169 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 72 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 169 (allA_of_3_1 71 71 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 169 (allA_succ_of_accept 69 70 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 169 (accept_3_3 68 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 169 (Polychromatic418967fa.accept_15_6_10_4_1_150 66 70 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 169 (accept_3_3 65 70 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 169 (accept_3_3 62 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 169 (Polychromatic418967fa.accept_16_13_6_9_1_2561 61 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 169 (Polychromatic418967fa.accept_22_16_4_15_1_7881 60 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 169 (accept_3_3 59 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 169 (Polychromatic418967fa.accept_15_13_10_4_1_1232 58 70
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 169 (accept_3_3 56 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  70 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 70 169 (Polychromatic418967fa.accept_15_9_10_4_1_2055 54 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 169 (accept_3_3 53 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 70 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 169 (accept_3_3 50 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  70 169 (Polychromatic418967fa.accept_19_11_13_17_1_9466 49 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 70 169 (Polychromatic418967fa.accept_17_14_2_16_1_4380 48 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 169 (accept_3_3 47 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 169 (Polychromatic418967fa.accept_20_6_10_9_1_3486 46 70
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 169 (accept_3_3 44 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 169 (Polychromatic418967fa.accept_17_8_2_16_1_5598 42 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 169 (accept_3_3 41 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 70 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 169 (accept_3_3 38 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 169 (Polychromatic418967fa.accept_15_7_10_4_1_151 37 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 169 (Polychromatic418967fa.accept_15_6_10_4_1_150 36 70 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 169 (accept_3_3 35 70 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 169 (Polychromatic418967fa.accept_16_2_6_9_1_3473 34 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 169 (accept_3_3 32 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 169 (Polychromatic418967fa.accept_19_11_13_17_1_9466 30 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 169 (accept_3_3 29 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 70 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 169 (accept_3_3 26 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 169 (Polychromatic418967fa.accept_17_8_2_16_1_5598 25 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 169 (Polychromatic418967fa.accept_15_9_10_4_1_2055 24 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 169 (accept_3_3 23 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 169 (Polychromatic418967fa.accept_15_7_10_4_1_151 22 70 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 70 169 (accept_3_3 20 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 169 (Polychromatic418967fa.accept_16_2_6_9_1_3473 18 70 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 169 (accept_3_3 17 70 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 70 169 (accept_3_3 14 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 169 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 169 (Polychromatic418967fa.accept_21_12_7_1_1_9465 12 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 169 (accept_3_3 11 70 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 169 (Polychromatic418967fa.accept_21_10_7_1_1_9464 10 70
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 169 (accept_3_3 8 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 70 169 (Polychromatic418967fa.accept_15_6_10_4_1_150 6 70 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 169 (accept_3_3 5 70 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 70 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 70 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 169 (accept_3_3 2 70 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 169 (Polychromatic418967fa.accept_17_1_2_16_1_5596
  1 70 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 169 (allA_succ_of_accept 68 69
  169 (accept_3_3 68 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 169
  (Polychromatic418967fa.accept_9_4_6_7_1_286 67 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 69 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 69 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 169 (accept_3_3 65 69 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 69 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 169 (Polychromatic418967fa.accept_12_3_9_1_1_290
  63 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 169 (accept_3_3 62
  69 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 169
  (Polychromatic418967fa.accept_7_5_6_1_1_407 61 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 69 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 69 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 169 (accept_3_3 59 69 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 69 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 69 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 57
  69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 169 (accept_3_3 56 69
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 169
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 69 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 69 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 169 (accept_3_3 53 69 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 69 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 51
  69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 169 (accept_3_3 50 69
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 169
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 69 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 69 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 169 (accept_3_3 47 69 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 69 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 69 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 169 (Polychromatic418967fa.accept_16_13_5_9_1_4682
  45 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 169 (accept_3_3 44
  69 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 169
  (Polychromatic418967fa.accept_15_13_9_4_1_3892 43 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 69 169 (Polychromatic418967fa.accept_15_12_9_4_1_3898 42 69 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 169 (accept_3_3 41 69 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 69 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 39
  69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 169 (accept_3_3 38 69
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 169 (Polychromatic418967fa.accept_7_2_6_1_1_73
  37 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 169
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 69 169 (accept_3_3 35 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  69 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 69 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 69 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 169 (accept_3_3 32 69 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 69 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 169
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 69 169 (accept_3_3 29 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  69 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 69 169 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 69 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 169 (accept_3_3 26 69 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 169 (Polychromatic418967fa.accept_15_10_9_4_1_2924 25 69 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 169
  (Polychromatic418967fa.accept_19_5_12_17_1_8089 24 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 69 169 (accept_3_3 23 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  69 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 69 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 69 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 169 (accept_3_3 20 69 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 69 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 169
  (Polychromatic418967fa.accept_11_7_3_4_1_729 18 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 69 169 (accept_3_3 17 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  69 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 69 169 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 69 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 169 (accept_3_3 14 69 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 69 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 169
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 69 169 (accept_3_3 11 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  69 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 69 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 69 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 169 (accept_3_3 8 69 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 169 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 69 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 169
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 6 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 169 (accept_3_3 5 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69
  169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 69 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 69 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 169 (accept_3_3 2 69 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 69 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 69 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 169 (allA_of_3_1 68 68 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 169 (allA_succ_of_accept 66 67 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 169 (accept_3_3 65 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 169 (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 169 (accept_3_3 62 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 67 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 169 (accept_3_3 59 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 169 (accept_3_3 56 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 67 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 169 (accept_3_3 53 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 169 (accept_3_3 50 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 169 (Polychromatic418967fa.accept_21_7_4_1_1_3300 49 67 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 169 (accept_3_3 47 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 169 (accept_3_3 44 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 169 (Polychromatic418967fa.accept_27_16_13_7_1_9463 43 67 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 169 (accept_3_3 41 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 169 (accept_3_3 38 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 67 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 169
  (Polychromatic418967fa.accept_20_16_7_9_1_9462 36 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 169 (accept_3_3 35 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 169 (accept_3_3 32 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 67 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 169 (accept_3_3 29 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 169 (Polychromatic418967fa.accept_15_12_7_4_1_2921 27 67 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 169 (accept_3_3 26 67 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 169 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 67
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 169
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 169 (accept_3_3 23 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 169 (accept_3_3 20 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 67 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 169 (accept_3_3 17 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 169 (Polychromatic418967fa.accept_20_16_7_9_1_9462 16 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 169 (accept_3_3 14 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 169 (Polychromatic418967fa.accept_21_13_4_1_1_942 13 67 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 169
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 169 (accept_3_3 11 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 169 (Polychromatic418967fa.accept_22_9_1_15_1_9461 9 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 169 (accept_3_3 8 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 169 (Polychromatic418967fa.accept_16_7_3_9_1_2557 7 67 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 169 (accept_3_3 5 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  169 (Polychromatic418967fa.accept_14_4_11_1_1_940 4 67 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 169 (accept_3_3 2 67 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 67 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 169 (allA_succ_of_accept 65 66
  169 (accept_3_3 65 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 169
  (Polychromatic418967fa.accept_9_1_3_7_1_6 64 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 66 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 169 (accept_3_3 62 66 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 66 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 66 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 60
  66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 169 (accept_3_3 59 66
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 169 (Polychromatic418967fa.accept_7_2_3_1_1_10
  58 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 66 169
  (Polychromatic418967fa.accept_18_3_12_7_1_6728 57 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 66 169 (accept_3_3 56 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  66 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 66 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 66 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 169 (accept_3_3 53 66 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 169 (Polychromatic418967fa.accept_17_1_15_16_1_2202 52 66 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 66 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 66 169 (accept_3_3 50 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  66 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 66 169 (Polychromatic418967fa.accept_17_14_15_16_1_1271 48 66 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 169 (accept_3_3 47 66 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 66 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 66 169
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 66 169 (accept_3_3 44 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  66 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 66 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 66 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 169 (accept_3_3 41 66 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 66 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 66 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 66 169 (accept_3_3 38 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  66 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 66 169 (Polychromatic418967fa.accept_21_15_3_1_1_6338 36 66 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 169 (accept_3_3 35 66 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 169 (Polychromatic418967fa.accept_20_14_6_9_1_9460 34 66
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 66 169
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 66 169 (accept_3_3 32 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  66 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 66 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 66 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 169 (accept_3_3 29 66 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 66 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 66 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 66 169 (accept_3_3 26 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  66 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 66 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 66 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 169 (accept_3_3 23 66 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 66 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 66 169
  (Polychromatic418967fa.accept_17_4_15_16_1_3231 21 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 66 169 (accept_3_3 20 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  66 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 66 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 66 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 169 (accept_3_3 17 66 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 66 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 66 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 66 169 (accept_3_3 14 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  66 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 66 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 66 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 169 (accept_3_3 11 66 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 66 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 169
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 169 (accept_3_3 8 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66
  169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 66 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 66 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 169 (accept_3_3 5 66 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 66 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 66 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 169 (accept_3_3 2 66 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 66
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 169 (allA_of_3_1 65 65 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 169 (allA_succ_of_accept 63 64 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 169 (accept_3_3 62 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 169 (Polychromatic418967fa.accept_22_17_20_15_1_9459 61 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 64 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 169 (accept_3_3 59 64 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 64 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 169 (accept_3_3 56 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 169 (Polychromatic418967fa.accept_10_5_4_9_1_420 55 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 169 (Polychromatic418967fa.accept_17_3_13_16_1_2183 54 64 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 169 (accept_3_3 53 64 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 169 (Polychromatic418967fa.accept_25_2_14_19_1_9458 52 64
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 169 (accept_3_3 50 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 64 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 169 (accept_3_3 47 64 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 169 (Polychromatic418967fa.accept_11_2_9_4_1_310 46 64 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 169 (accept_3_3 44 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 169 (Polychromatic418967fa.accept_10_3_4_9_1_15 43 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 64 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 169 (accept_3_3 41 64 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 64 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 169 (accept_3_3 38 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 169 (Polychromatic418967fa.accept_14_9_8_1_1_2381 37 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 169 (Polychromatic418967fa.accept_23_13_18_8_1_9457 36 64 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 169 (accept_3_3 35 64 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 64
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 169 (accept_3_3 32 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 64 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 169 (accept_3_3 29 64 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 169 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 64 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 169 (accept_3_3 26 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 169 (Polychromatic418967fa.accept_10_5_4_9_1_420 25 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 64 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 169 (accept_3_3 23 64 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 64 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 169 (accept_3_3 20 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 169 (Polychromatic418967fa.accept_20_19_4_9_1_5025 19 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 169 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 64 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 169 (accept_3_3 17 64 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 169 (Polychromatic418967fa.accept_14_2_8_1_1_1647 16 64 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 169 (accept_3_3 14 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 64 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 169 (accept_3_3 11 64 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 64 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 169 (accept_3_3 8 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  169 (Polychromatic418967fa.accept_14_7_8_1_1_1621 7 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 64 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 64 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 169 (accept_3_3 5 64 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 64 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 64 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 64 169 (accept_3_3 2 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64
  169 (Polychromatic418967fa.accept_26_1_12_13_1_9456 1 64 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 64 169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 169
  (allA_succ_of_accept 62 63 169 (accept_3_3 62 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  63 169 (Polychromatic418967fa.accept_15_1_3_4_1_1217 61 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 63 169 (Polychromatic418967fa.accept_18_6_9_7_1_2905 60 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 169 (accept_3_3 59 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 169
  (Polychromatic418967fa.accept_12_9_3_1_1_303 57 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 63 169 (accept_3_3 56 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  63 169 (Polychromatic418967fa.accept_14_13_7_1_1_1618 55 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 63 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 169 (accept_3_3 53 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 169
  (Polychromatic418967fa.accept_11_7_8_4_1_718 51 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 169 (accept_3_3 50 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 169 (Polychromatic418967fa.accept_19_11_6_17_1_9455 49 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 169 (Polychromatic418967fa.accept_14_6_7_1_1_78 48 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 169 (accept_3_3 47 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 169
  (Polychromatic418967fa.accept_11_1_8_4_1_717 45 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 169 (accept_3_3 44 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 169 (Polychromatic418967fa.accept_27_16_9_7_1_9454 43 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 169 (accept_3_3 41 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 169
  (Polychromatic418967fa.accept_18_3_9_7_1_1839 39 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 169 (accept_3_3 38 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 169 (Polychromatic418967fa.accept_15_7_3_4_1_574 37 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 169 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 169 (accept_3_3 35 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 169
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 169 (accept_3_3 32 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 169 (Polychromatic418967fa.accept_15_1_3_4_1_1217 31 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 169 (accept_3_3 29 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 169
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 169 (accept_3_3 26 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 169 (Polychromatic418967fa.accept_22_3_19_15_1_7831 25 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 169 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 169 (accept_3_3 23 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 169
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 169 (accept_3_3 20 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 169 (Polychromatic418967fa.accept_20_19_3_9_1_7965 19 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 169 (accept_3_3 17 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 169
  (Polychromatic418967fa.accept_20_15_3_9_1_5007 15 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 169 (accept_3_3 14 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 169 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 169 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 169 (accept_3_3 11 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 169
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 169 (accept_3_3 8 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  169 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 169 (accept_3_3 5 63 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 63 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 169 (Polychromatic418967fa.accept_18_3_9_7_1_1839 3
  63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 169 (accept_3_3 2 63 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 169 (Polychromatic418967fa.accept_11_1_8_4_1_717 1
  63 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 169 (allA_of_3_1 62 62 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 169 (allA_succ_of_accept 60 61 169
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 169 (accept_3_3 59 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 169 (Polychromatic418967fa.accept_10_8_1_9_1_413 58 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 169 (Polychromatic418967fa.accept_11_2_6_4_1_3028 57 61 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 169 (accept_3_3 56 61 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 61 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 169
  (Polychromatic418967fa.accept_16_6_13_9_1_4690 54 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 169 (accept_3_3 53 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 169 (Polychromatic418967fa.accept_19_13_4_17_1_5166 51 61 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 169 (accept_3_3 50 61 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 169 (Polychromatic418967fa.accept_16_1_13_9_1_2551 49 61
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 169
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 169 (accept_3_3 47 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 61 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 169 (accept_3_3 44 61 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 169 (Polychromatic418967fa.accept_17_9_10_16_1_3217 43 61 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 169
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 169 (accept_3_3 41 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 169 (Polychromatic418967fa.accept_17_6_10_16_1_9453 40 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 61 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 169 (accept_3_3 38 61 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 169 (Polychromatic418967fa.accept_16_5_13_9_1_2594 37 61 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 169
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 169 (accept_3_3 35 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 169 (Polychromatic418967fa.accept_15_3_1_4_1_1246 33 61 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 169 (accept_3_3 32 61 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 61 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 169
  (Polychromatic418967fa.accept_19_11_4_17_1_2617 30 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 169 (accept_3_3 29 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 61 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 169 (accept_3_3 26 61 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 61 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 169
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 169 (accept_3_3 23 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 169 (Polychromatic418967fa.accept_10_2_1_9_1_1248 22 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 169 (Polychromatic418967fa.accept_16_5_13_9_1_2594 21 61 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 169 (accept_3_3 20 61 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 169 (Polychromatic418967fa.accept_24_19_13_1_1_9452 19 61
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 169
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 169 (accept_3_3 17 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 169 (Polychromatic418967fa.accept_21_16_19_1_1_6320 16 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 169 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 61 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 169 (accept_3_3 14 61 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 61 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 169
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 169 (accept_3_3 11 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 169 (Polychromatic418967fa.accept_17_9_10_16_1_3217 9 61 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 169 (accept_3_3 8 61 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 169 (Polychromatic418967fa.accept_16_7_13_9_1_1653 7 61 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 169
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 169 (accept_3_3 5 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  169 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 61 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 61 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 169 (accept_3_3 2 61 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 169 (Polychromatic418967fa.accept_16_1_13_9_1_2551 1 61 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 169 (allA_succ_of_accept 59 60 169 (accept_3_3 59 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 60 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 60 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 60 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 169 (accept_3_3 56 60 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 55
  60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 169
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 169 (accept_3_3 53 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  60 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 169 (Polychromatic418967fa.accept_16_3_12_9_1_8250 51 60 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 169 (accept_3_3 50 60 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 60 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 60 169 (accept_3_3 47 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  60 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 60 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 60 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 60 169 (accept_3_3 44 60 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 169 (Polychromatic418967fa.accept_11_10_5_4_1_711 43 60 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 169
  (Polychromatic418967fa.accept_17_8_9_16_1_6844 42 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 60 169 (accept_3_3 41 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  60 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 60 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 60 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 169 (accept_3_3 38 60 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 60 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 169
  (Polychromatic418967fa.accept_16_4_12_9_1_2567 36 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 60 169 (accept_3_3 35 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  60 169 (Polychromatic418967fa.accept_16_2_12_9_1_2568 34 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 60 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 60 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 169 (accept_3_3 32 60 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 60 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 60 169 (accept_3_3 29 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  60 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 60 169 (Polychromatic418967fa.accept_17_10_9_16_1_5607 27 60 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 169 (accept_3_3 26 60 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 169 (Polychromatic418967fa.accept_14_11_4_1_1_4255 25 60
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 169
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 169 (accept_3_3 23 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  60 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 60 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 169 (accept_3_3 20 60 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 60 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 169
  (Polychromatic418967fa.accept_16_2_12_9_1_2568 18 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 169 (accept_3_3 17 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  60 169 (Polychromatic418967fa.accept_19_16_3_17_1_6575 16 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 60 169 (Polychromatic418967fa.accept_19_15_3_17_1_9451 15 60 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 169 (accept_3_3 14 60 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 60 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 169
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 169 (accept_3_3 11 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  60 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 60 169 (Polychromatic418967fa.accept_18_9_6_7_1_6719 9 60 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 169 (accept_3_3 8 60 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 169 (Polychromatic418967fa.accept_26_7_8_13_1_9450 7 60 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 169
  (Polychromatic418967fa.accept_17_6_9_16_1_4410 6 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 60 169 (accept_3_3 5 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60
  169 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 60 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 60 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 60 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 169 (accept_3_3 2 60 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 60 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 60 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 169 (allA_of_3_1 59 59 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 169
  (allA_succ_of_accept 57 58 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 58 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 169 (accept_3_3 56 58 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 169 (Polychromatic418967fa.accept_10_4_8_9_1_784
  54 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 169 (accept_3_3 53
  58 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 52 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 169 (accept_3_3 50 58 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 169 (Polychromatic418967fa.accept_16_1_10_9_1_4645 49 58 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 169
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 58 169 (accept_3_3 47 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  58 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 58 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 58 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 169 (accept_3_3 44 58 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 58 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 58 169 (accept_3_3 41 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  58 169 (Polychromatic418967fa.accept_11_7_3_4_1_729 40 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 58 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 169 (accept_3_3 38 58 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 58 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 169
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 169 (accept_3_3 35 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 58 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 169 (accept_3_3 32 58 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 169 (accept_3_3 29 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 169 (accept_3_3 26 58 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 169 (Polychromatic418967fa.accept_15_10_13_4_1_1210 25 58 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 169 (accept_3_3 23 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 169 (Polychromatic418967fa.accept_14_8_2_1_1_1652 22 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 58 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 169 (accept_3_3 20 58 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 169
  (Polychromatic418967fa.accept_11_7_3_4_1_729 18 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 169 (accept_3_3 17 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 169 (accept_3_3 14 58 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 58 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 169 (accept_3_3 11 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 58 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 169 (accept_3_3 8 58 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 169
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 169 (accept_3_3 5 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  169 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 58 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 58 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 169 (accept_3_3 2 58 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 58 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 58 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 169))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 57 169 (allA_succ_of_accept 56 57 169 (accept_3_3 56 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 57 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 57 169 (Polychromatic418967fa.accept_15_9_12_4_1_2023 54 57
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 169 (accept_3_3 53 57 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 52
  57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 57 169 (accept_3_3 50 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  57 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 57 169 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 57 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 169 (accept_3_3 47 57 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 57 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 169
  (Polychromatic418967fa.accept_18_9_3_7_1_9449 45 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 57 169 (accept_3_3 44 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  57 169 (Polychromatic418967fa.accept_17_9_6_16_1_3280 43 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 57 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 57 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 169 (accept_3_3 41 57 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 169
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 57 169 (accept_3_3 38 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  57 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 57 169 (Polychromatic418967fa.accept_22_14_13_15_1_9448 36 57 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 169 (accept_3_3 35 57 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 57 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 57 169 (accept_3_3 32 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  57 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 57 169 (Polychromatic418967fa.accept_18_12_3_7_1_5373 30 57 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 169 (accept_3_3 29 57 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 169
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 57 169 (accept_3_3 26 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  57 169 (Polychromatic418967fa.accept_27_25_3_7_1_9447 25 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 57 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 57 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 169 (accept_3_3 23 57 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 57 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 169
  (Polychromatic418967fa.accept_25_21_7_19_1_7578 21 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 57 169 (accept_3_3 20 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  57 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 57 169 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 57 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 169 (accept_3_3 17 57 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 169 (accept_3_3 14 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  57 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 57 169 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 57 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 169 (accept_3_3 11 57 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 57 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 169
  (Polychromatic418967fa.accept_11_9_2_4_1_707 9 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 57 169 (accept_3_3 8 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57
  169 (Polychromatic418967fa.accept_15_7_12_4_1_1236 7 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 57 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 57 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 169 (accept_3_3 5 57 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 169
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 57 169 (accept_3_3 2 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57
  169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 57 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 57 169))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 169 (allA_of_3_1 56 56 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 169 (allA_succ_of_accept 54 55 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 169 (accept_3_3 53 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 169 (Polychromatic418967fa.accept_15_7_10_4_1_151 52 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 55 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 169 (accept_3_3 50 55 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 55 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 169
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 169 (accept_3_3 47 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 169 (Polychromatic418967fa.accept_16_13_7_9_1_2606 45 55 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 169 (accept_3_3 44 55 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 169 (Polychromatic418967fa.accept_15_13_10_4_1_1232 43 55
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 169 (accept_3_3 41 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 55 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 169 (accept_3_3 38 55 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 55 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 169
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 169 (accept_3_3 35 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 55 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 169 (accept_3_3 32 55 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 55 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 169 (accept_3_3 29 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 169 (Polychromatic418967fa.accept_15_13_10_4_1_1232 28 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 169 (Polychromatic418967fa.accept_22_5_11_15_1_7870 27 55 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 169 (accept_3_3 26 55 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 169 (Polychromatic418967fa.accept_20_5_15_9_1_9446 25 55
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 169
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 169 (accept_3_3 23 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 55 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 169 (accept_3_3 20 55 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 55 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 169 (accept_3_3 17 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 55 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 169 (accept_3_3 14 55 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 55 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 169
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 169 (accept_3_3 11 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 55 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 169 (accept_3_3 8 55 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 169 (Polychromatic418967fa.accept_14_7_13_1_1_922 7 55 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 169 (accept_3_3 5 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  169 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 55 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 55 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 169 (accept_3_3 2 55 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 169 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 55 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 169)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 169 (allA_succ_of_accept 53 54 169 (accept_3_3 53 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 54 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 54 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 169 (accept_3_3 50 54 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 169 (Polychromatic418967fa.accept_11_5_10_4_1_1157
  49 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 169
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 169 (accept_3_3 47 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 54 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 169 (accept_3_3 44 54 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 169
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 42 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 169 (accept_3_3 41 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 169 (Polychromatic418967fa.accept_15_10_9_4_1_2924 40 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 169 (accept_3_3 38 54 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 169 (Polychromatic418967fa.accept_19_18_16_17_1_2626 37 54 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 169
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 36 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 169 (accept_3_3 35 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 169 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 54 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 169 (accept_3_3 32 54 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 169
  (Polychromatic418967fa.accept_17_13_3_16_1_5599 30 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 169 (accept_3_3 29 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 169 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 169 (accept_3_3 26 54 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 54 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 169
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 169 (accept_3_3 23 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 169 (Polychromatic418967fa.accept_19_3_16_17_1_3826 22 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 169 (Polychromatic418967fa.accept_15_6_9_4_1_1227 21 54 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 169 (accept_3_3 20 54 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 169
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 169 (accept_3_3 17 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 169 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 169 (accept_3_3 14 54 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 54 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 169
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 169 (accept_3_3 11 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 169 (Polychromatic418967fa.accept_21_9_12_1_1_7926 9 54 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 169 (accept_3_3 8 54 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 169
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 169 (accept_3_3 5 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  169 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 54 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 54 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 169 (accept_3_3 2 54 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 54 169 (Polychromatic418967fa.accept_19_1_16_17_1_3864 1 54 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 169))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 169 (allA_of_3_1 53 53 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 169
  (allA_succ_of_accept 51 52 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 169 (accept_3_3 50 52 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 169 (Polychromatic418967fa.accept_17_15_1_16_1_8166 49 52 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 169
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 48 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 169 (accept_3_3 47 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 169 (accept_3_3 44 52 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 169 (Polychromatic418967fa.accept_16_11_4_9_1_851 43 52 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 169
  (Polychromatic418967fa.accept_15_12_7_4_1_2921 42 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 169 (accept_3_3 41 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 52 169 13 3 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 52 169 (accept_3_3 38 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 52 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 52 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 169 (Polychromatic418967fa.accept_17_2_1_16_1_6946 36 52
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 169 (accept_3_3 35 52 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 169 (Polychromatic418967fa.accept_11_1_8_4_1_717
  34 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 52 169 (accept_3_3 32 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  52 169 (Polychromatic418967fa.accept_10_1_2_9_1_152 31 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 52 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 52 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 169 (accept_3_3 29 52 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 169 (Polychromatic418967fa.accept_16_12_4_9_1_4633 28 52 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 52 169 13 2 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 52 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 52 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 169 (Polychromatic418967fa.accept_16_8_4_9_1_4666 24 52 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 169 (accept_3_3 23 52 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843
  22 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 52 169 (accept_3_3 20 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  52 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 52 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 52 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 169 (accept_3_3 17 52 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 52 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 169 (accept_3_3 14 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 52
  169 13 1 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12
  52 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 52 169 (accept_3_3 11 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 52 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 52 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 169 (accept_3_3 8 52 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 169 (Polychromatic418967fa.accept_10_7_2_9_1_775 7
  52 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 169
  (Polychromatic418967fa.accept_22_6_8_15_1_6038 6 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 169 (accept_3_3 5 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  169 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 52 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 169 (accept_3_3 2 52 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 169 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 52 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 169))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 169 (allA_succ_of_accept 50 51 169 (accept_3_3 50 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 51 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 51 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 169 (accept_3_3 47 51 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 46
  51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 169 (accept_3_3 44 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 169 (Polychromatic418967fa.accept_15_13_6_4_1_1221 43 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 169 (accept_3_3 41 51 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 169 (accept_3_3 38 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 169 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 51 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 169 (accept_3_3 35 51 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 169
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 169 (accept_3_3 32 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 169 (accept_3_3 29 51 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 169
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 169 (accept_3_3 26 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 169 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 51 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 169 (accept_3_3 23 51 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 169 (accept_3_3 20 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 169 (accept_3_3 17 51 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 169
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 169 (accept_3_3 14 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 51 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 169 (accept_3_3 11 51 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 169
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 169 (accept_3_3 8 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  169 (Polychromatic418967fa.accept_16_7_3_9_1_2557 7 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 51 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 169 (accept_3_3 5 51 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 51 169 (accept_3_3 2 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51
  169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 51 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 169))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 169 (allA_of_3_1 50 50 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 49 169 (allA_succ_of_accept 48 49 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 49 169 (accept_3_3 47 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  49 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 49 169 (Polychromatic418967fa.accept_16_13_1_9_1_2597 45 49 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 169 (accept_3_3 44 49 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 169 (Polychromatic418967fa.accept_11_10_5_4_1_711 43 49 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 169 (accept_3_3 41 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 169 (Polychromatic418967fa.accept_16_8_1_9_1_847 40 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 49 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 169 (accept_3_3 38 49 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 49 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 169
  (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 169 (accept_3_3 35 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 169 (Polychromatic418967fa.accept_14_6_7_1_1_78 34 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 49 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 169 (accept_3_3 32 49 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 169 (Polychromatic418967fa.accept_17_14_15_16_1_1271 31 49 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 169 (accept_3_3 29 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 169 (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 49 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 169 (accept_3_3 26 49 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 169 (Polychromatic418967fa.accept_19_6_11_17_1_2611 25 49
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 169 (accept_3_3 23 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 169 (Polychromatic418967fa.accept_14_8_7_1_1_1615 22 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 49 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 169 (accept_3_3 20 49 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 49 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 169
  (Polychromatic418967fa.accept_16_2_1_9_1_2577 18 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 169 (accept_3_3 17 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 169 (Polychromatic418967fa.accept_21_16_7_1_1_9430 16 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 49 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 169 (accept_3_3 14 49 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 169 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 49 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 169
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 169 (accept_3_3 11 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 169 (Polychromatic418967fa.accept_19_9_11_17_1_9445 9 49 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 169 (accept_3_3 8 49 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 169 (Polychromatic418967fa.accept_28_7_21_1_1_9444 7 49 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 169 (accept_3_3 5 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  169 (Polychromatic418967fa.accept_17_4_15_16_1_3231 4 49 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 49 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 169 (accept_3_3 2 49 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 169)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 169 (allA_succ_of_accept 47 48 169 (accept_3_3 47 48 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 48 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 169 (Polychromatic418967fa.accept_17_11_14_16_1_1270 45 48
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 169 (accept_3_3 44 48 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 169
  (Polychromatic418967fa.accept_22_21_4_15_1_9443 43 48 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 48 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 48 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 169 (accept_3_3 41 48 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 48 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 48 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 48 169 (Polychromatic418967fa.accept_18_3_12_7_1_6728
  39 48 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 169 (accept_3_3 38
  48 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 169
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 48 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 48 169 (Polychromatic418967fa.accept_17_2_14_16_1_2187 36 48 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 169 (accept_3_3 35 48 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 48 169 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 48 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 48 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 33
  48 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 169 (accept_3_3 32 48
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 169
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 48 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 48 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 48 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 169 (accept_3_3 29 48 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 48 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 48 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 48 169 (Polychromatic418967fa.accept_10_7_8_9_1_785
  27 48 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 169 (accept_3_3 26
  48 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 169
  (Polychromatic418967fa.accept_17_8_14_16_1_6849 25 48 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 48 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 48 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 169 (accept_3_3 23 48 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 48 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 48 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 48 169 (Polychromatic418967fa.accept_10_1_8_9_1_787
  21 48 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 169 (accept_3_3 20
  48 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 169
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 48 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 48 169 (Polychromatic418967fa.accept_19_18_10_17_1_5192 18 48 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 169 (accept_3_3 17 48 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 48 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 48 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 48 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 15
  48 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 169 (accept_3_3 14 48
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 169
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 48 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 48 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 48 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 169 (accept_3_3 11 48 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 48 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 48 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 48 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 48
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 169 (accept_3_3 8 48 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 169 (Polychromatic418967fa.accept_10_7_8_9_1_785 7
  48 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 48 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 169 (accept_3_3 5 48 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  169 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 48 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 169 (Polychromatic418967fa.accept_18_3_12_7_1_6728 3 48 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 169 (accept_3_3 2 48 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 48 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 169)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 169 (allA_of_3_1 47 47 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 169 (allA_succ_of_accept 45 46
  169 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 169 (accept_3_3 44 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 46 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 169 (accept_3_3 41 46 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 46 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 169 (accept_3_3 38 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 169 (Polychromatic418967fa.accept_16_5_14_9_1_2572 37 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 169 (Polychromatic418967fa.accept_16_4_14_9_1_4657 36 46 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 169 (accept_3_3 35 46 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 169 (Polychromatic418967fa.accept_19_15_8_17_1_9429 34 46
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 169 (accept_3_3 32 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 46 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 169 (accept_3_3 29 46 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 169 (Polychromatic418967fa.accept_11_6_2_4_1_1703 28 46 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 169 (accept_3_3 26 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 169 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 46 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 169 (accept_3_3 23 46 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 46 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 169 (accept_3_3 20 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 169 (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 46 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 169 (accept_3_3 17 46 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 46 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 169 (accept_3_3 14 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 46 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 169 (accept_3_3 11 46 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 46 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 169 (accept_3_3 8 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 46 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 169 (accept_3_3 5 46 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 46 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 169 (accept_3_3 2 46 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 169 (Polychromatic418967fa.accept_17_1_12_16_1_2211
  1 46 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  169)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 169 (allA_succ_of_accept 44 45 169 (accept_3_3 44 45
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 169
  (Polychromatic418967fa.accept_19_5_7_17_1_9442 43 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 169 (Polychromatic418967fa.accept_18_6_9_7_1_2905 42 45 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 169 (accept_3_3 41 45 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 39
  45 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 169 (accept_3_3 38 45
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 169 (Polychromatic418967fa.accept_7_2_3_1_1_10
  37 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 169
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 169 (accept_3_3 35 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 45 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 169 (accept_3_3 32 45 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 169 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 45 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 169
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 169 (accept_3_3 29 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 169 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 45 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 169 (accept_3_3 26 45 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 169 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 45 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 169
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 169 (accept_3_3 23 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 169 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 45 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 169 (accept_3_3 20 45 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 45 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 169
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 169 (accept_3_3 17 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 169 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 45 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 169 (accept_3_3 14 45 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 169 (Polychromatic418967fa.accept_19_13_7_17_1_9441 13 45 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 169
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 169 (accept_3_3 11 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 45 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 169 (accept_3_3 8 45 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 169 (Polychromatic418967fa.accept_16_7_13_9_1_1653 7 45 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 169
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 169 (accept_3_3 5 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 169 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 45 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 169 (accept_3_3 2 45 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 169 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 45 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 169))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  169 (allA_of_3_1 44 44 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 169 (allA_succ_of_accept 42 43 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 169 (accept_3_3 41 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 169 (Polychromatic418967fa.accept_15_10_13_4_1_1210 40 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 169 (Polychromatic418967fa.accept_15_9_13_4_1_1209 39 43 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 169 (accept_3_3 38 43 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 169 (Polychromatic418967fa.accept_16_5_11_9_1_861 37 43 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 169
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 169 (accept_3_3 35 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 169 (Polychromatic418967fa.accept_19_14_5_17_1_6542 33 43 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 169 (accept_3_3 32 43 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 169 (Polychromatic418967fa.accept_19_12_5_17_1_9439 31 43
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 169 (accept_3_3 29 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 169 (Polychromatic418967fa.accept_22_6_21_15_1_9440 28 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 169 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 43 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 169 (accept_3_3 26 43 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 169 (Polychromatic418967fa.accept_15_10_13_4_1_1210 25 43
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 169
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 169 (accept_3_3 23 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 169 (Polychromatic418967fa.accept_15_6_13_4_1_2040 21 43 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 169 (accept_3_3 20 43 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 169 (Polychromatic418967fa.accept_20_19_3_9_1_7965 19 43
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 169 (accept_3_3 17 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 169 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 169 (Polychromatic418967fa.accept_19_15_5_17_1_8036 15 43 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 169 (accept_3_3 14 43 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 169 (Polychromatic418967fa.accept_17_13_9_16_1_3254 13 43
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 169
  (Polychromatic418967fa.accept_19_12_5_17_1_9439 12 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 169 (accept_3_3 11 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 169 (Polychromatic418967fa.accept_15_9_13_4_1_1209 9 43 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 169 (accept_3_3 8 43 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 169 (Polychromatic418967fa.accept_19_7_5_17_1_3849 7 43 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 169 (accept_3_3 5 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  169 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 43 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 43 169 (Polychromatic418967fa.accept_19_3_5_17_1_9438 3 43 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 169 (accept_3_3 2 43 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 169 (Polychromatic418967fa.accept_25_1_18_19_1_9437 1 43 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 169)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 42 169 (allA_succ_of_accept 41 42 169 (accept_3_3 41 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 42 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 42 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 169 (accept_3_3 38 42 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 37
  42 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 169
  (Polychromatic418967fa.accept_17_2_8_16_1_4403 36 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 169 (accept_3_3 35 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 169 (Polychromatic418967fa.accept_23_11_19_8_1_9436 34 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 169 (Polychromatic418967fa.accept_16_1_10_9_1_4645 33 42 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 169 (accept_3_3 32 42 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 169 (accept_3_3 29 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 169 (accept_3_3 26 42 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 169 (Polychromatic418967fa.accept_19_6_4_17_1_6540 25 42 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 169
  (Polychromatic418967fa.accept_11_2_9_4_1_310 24 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 169 (accept_3_3 23 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 42 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 169 (accept_3_3 20 42 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 169
  (Polychromatic418967fa.accept_19_18_4_17_1_2618 18 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 169 (accept_3_3 17 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 169 (Polychromatic418967fa.accept_15_1_12_4_1_2022 16 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 169 (accept_3_3 14 42 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 42 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 169 (accept_3_3 11 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 169 (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 42 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 169 (accept_3_3 8 42 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 169
  (Polychromatic418967fa.accept_19_6_4_17_1_6540 6 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 169 (accept_3_3 5 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  169 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 42 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 169 (accept_3_3 2 42 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 42 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 169)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 169
  (allA_of_3_1 41 41 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 169 (allA_succ_of_accept 39 40 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 169 (accept_3_3 38 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 169 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 40 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 169 (accept_3_3 35 40 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 40 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 169 (accept_3_3 32 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 40 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 169 (accept_3_3 29 40 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 40 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 169 (accept_3_3 26 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 40 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 169 (accept_3_3 23 40 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 40 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 169 (accept_3_3 20 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 40 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 169 (accept_3_3 17 40 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 169 (Polychromatic418967fa.accept_18_16_4_7_1_2927 16 40 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 169 (accept_3_3 14 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 40 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 169 (accept_3_3 11 40 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 40 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 169 (accept_3_3 8 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  169 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 40 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 40 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 169 (accept_3_3 5 40 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 40 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 40 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 169 (accept_3_3 2 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40
  169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 40 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 169)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 169 (allA_succ_of_accept 38 39 169 (accept_3_3
  38 39 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 169
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 39 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 169 (Polychromatic418967fa.accept_15_6_9_4_1_1227 36 39 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 169 (accept_3_3 35 39 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 33
  39 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 169 (accept_3_3 32 39
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 169 (Polychromatic418967fa.accept_7_3_4_1_1_71
  31 39 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 169 (accept_3_3 29 39 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 169 (Polychromatic418967fa.accept_15_12_9_4_1_3898 27 39 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 39 169 13 2 3 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 39 169
  (Polychromatic418967fa.accept_15_10_9_4_1_2924 25 39 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 39 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 39 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 169 (accept_3_3 23 39 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 39 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 169 (Polychromatic418967fa.accept_12_9_3_1_1_303
  21 39 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 169 (accept_3_3 20
  39 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 169
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 39 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 39 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 169 (accept_3_3 17 39 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 39 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 15
  39 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 169 (accept_3_3 14 39
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 39 169 13 1 3 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 39 169
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 39 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 169 (accept_3_3 11 39 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 169 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 39 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 169 (accept_3_3 8 39 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 169 (Polychromatic418967fa.accept_25_7_14_19_1_7601 7 39 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 169 (accept_3_3 5 39 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 39 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 169 (accept_3_3 2 39 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 39 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 169))))))))))))))))))))))))))))))))))))))) (allB_succ 38 169
  (allA_of_3_1 38 38 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 169 (allA_succ_of_accept 36 37 169
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 169 (accept_3_3 35 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 37 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 169 (accept_3_3 32 37 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 37 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 169
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 169 (accept_3_3 29 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 37 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 169 (accept_3_3 26 37 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 169 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 37 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 169 (accept_3_3 23 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 37 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 169 (accept_3_3 20 37 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 169 (Polychromatic418967fa.accept_21_19_16_1_1_2053 19 37 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 169
  (Polychromatic418967fa.accept_10_8_7_9_1_425 18 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 169 (accept_3_3 17 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 169 (Polychromatic418967fa.accept_18_16_1_7_1_4083 16 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 37 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 169 (accept_3_3 14 37 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 37 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 169
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 169 (accept_3_3 11 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 169 (Polychromatic418967fa.accept_23_9_14_8_1_9435 9 37 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 169 (accept_3_3 8 37 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 169 (Polychromatic418967fa.accept_17_7_3_16_1_2208 7 37 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 169
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 169 (accept_3_3 5 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  169 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 37 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 37 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 169 (accept_3_3 2 37 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 169 (Polychromatic418967fa.accept_16_1_5_9_1_1649 1 37 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 169))))))))))))))))))))))))))))))))))))) (allB_succ 36 169
  (allA_succ_of_accept 35 36 169 (accept_3_3 35 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  36 169 (Polychromatic418967fa.accept_22_12_14_15_1_9434 34 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 36 169 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 36 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 169 (accept_3_3 32 36 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 169 (Polychromatic418967fa.accept_17_14_2_16_1_4380 31 36 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 169
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 30 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 169 (accept_3_3 29 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 169 (Polychromatic418967fa.accept_15_13_6_4_1_1221 28 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 169 (Polychromatic418967fa.accept_16_11_4_9_1_851 27 36 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 169 (accept_3_3 26 36 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 169 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 36 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 169
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 169 (accept_3_3 23 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  36 169 (Polychromatic418967fa.accept_17_5_2_16_1_1294 22 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 36 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 169 (accept_3_3 20 36 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 169 (Polychromatic418967fa.accept_20_19_16_9_1_9433 19 36 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 169
  (Polychromatic418967fa.accept_11_7_3_4_1_729 18 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 36 169 (accept_3_3 17 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  36 169 (Polychromatic418967fa.accept_14_2_8_1_1_1647 16 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 36 169 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 36 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 169 (accept_3_3 14 36 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 36 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 169
  (Polychromatic418967fa.accept_16_12_4_9_1_4633 12 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 169 (accept_3_3 11 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 169 (Polychromatic418967fa.accept_15_10_6_4_1_1256 10 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 169 (Polychromatic418967fa.accept_14_9_8_1_1_2381 9 36 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 169 (accept_3_3 8 36 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 169 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 36 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 169
  (Polychromatic418967fa.accept_21_6_15_1_1_2050 6 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 169 (accept_3_3 5 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  169 (Polychromatic418967fa.accept_22_4_14_15_1_7828 4 36 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 36 169 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 36 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 169 (accept_3_3 2 36 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 169 (Polychromatic418967fa.accept_17_1_2_16_1_5596 1 36 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 169)))))))))))))))))))))))))))))))))))) (allB_succ 35
  169 (allA_of_3_1 35 35 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 169 (allA_succ_of_accept 33 34 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 34 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 169 (accept_3_3 32 34 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 34 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 169 (accept_3_3 29 34 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 169 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 34 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 169 (accept_3_3 26 34 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 169 (Polychromatic418967fa.accept_10_5_4_9_1_420 25 34 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 169 (Polychromatic418967fa.accept_19_5_15_17_1_9432 24 34 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 169 (accept_3_3 23 34 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 169 (Polychromatic418967fa.accept_16_6_2_9_1_5897 22 34 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 34 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 169 (accept_3_3 20 34 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 169 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 34 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 169 (accept_3_3 17 34 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 34 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 169 (accept_3_3 14 34 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 169 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 34 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 34 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 169 (accept_3_3 11 34 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 169 (Polychromatic418967fa.accept_19_10_15_17_1_6590 10 34 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 34 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 169 (accept_3_3 8 34 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 169 (Polychromatic418967fa.accept_16_6_2_9_1_5897 6 34 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 169 (accept_3_3 5 34 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 34 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 169 (accept_3_3 2 34 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 169 (Polychromatic418967fa.accept_16_1_2_9_1_1607 1
  34 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 169))))))))))))))))))))))))))))))))))
  (allB_succ 33 169 (allA_succ_of_accept 32 33 169 (accept_3_3 32 33 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 33 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 33 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 169 (accept_3_3 29 33 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  33 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 169
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 33 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 169 (accept_3_3 26 33 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 33 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 33 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 169 (accept_3_3 23 33 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 33 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 33 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 169 (accept_3_3 20 33 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 33 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 33 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 169 (accept_3_3 17 33 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 169
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 33 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 169 (accept_3_3 14 33 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 33 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 33 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 169 (accept_3_3 11 33 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 33 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 169
  (Polychromatic418967fa.accept_19_9_14_17_1_2613 9 33 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 169 (accept_3_3 8 33 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  169 (Polychromatic418967fa.accept_15_7_3_4_1_574 7 33 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 33 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 169 (accept_3_3 5 33 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 33
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 169 (accept_3_3 2 33 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  33 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 169)))))))))))))))))))))))))))))))))
  (allB_succ 32 169 (allA_of_3_1 32 32 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 169
  (allA_succ_of_accept 30 31 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 169 (accept_3_3 29 31 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 31 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 169 (Polychromatic418967fa.accept_15_12_1_4_1_2899
  27 31 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 169 (accept_3_3 26
  31 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 169
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 31 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 169 (accept_3_3 23 31 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 21
  31 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 169 (accept_3_3 20 31
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 169
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 31 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 169 (accept_3_3 17 31 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 31 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 15
  31 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 169 (accept_3_3 14 31
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 169
  (Polychromatic418967fa.accept_11_2_9_4_1_310 13 31 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 31 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 31 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 169 (accept_3_3 11 31 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 31 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 31
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 169 (accept_3_3 8 31 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 169 (Polychromatic418967fa.accept_21_7_10_1_1_6278
  7 31 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 169 (accept_3_3 5 31 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  169 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 31 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 31 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 169 (accept_3_3 2 31 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 31 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 169))))))))))))))))))))))))))))))) (allB_succ 30 169
  (allA_succ_of_accept 29 30 169 (accept_3_3 29 30 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  30 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 30 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 30 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 169 (accept_3_3 26 30 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 169 (Polychromatic418967fa.accept_19_6_11_17_1_2611 25 30 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 169
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 30 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 30 169 (accept_3_3 23 30 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  30 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 30 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 30 169 (Polychromatic418967fa.accept_16_5_14_9_1_2572 21 30 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 169 (accept_3_3 20 30 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 169
  (Polychromatic418967fa.accept_11_7_8_4_1_718 18 30 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 30 169 (accept_3_3 17 30 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  30 169 (Polychromatic418967fa.accept_20_16_10_9_1_9431 16 30 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 30 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 169 (accept_3_3 14 30 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 30 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 169
  (Polychromatic418967fa.accept_11_1_8_4_1_717 12 30 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 30 169 (accept_3_3 11 30 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  30 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 30 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 30 169 (Polychromatic418967fa.accept_17_9_13_16_1_3266 9 30 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 169 (accept_3_3 8 30 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 169
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 30 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 30 169 (accept_3_3 5 30 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30
  169 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 30 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 30 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 169 (accept_3_3 2 30 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 30 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 30 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 169)))))))))))))))))))))))))))))) (allB_succ 29 169 (allA_of_3_1
  29 29 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 169 (allA_succ_of_accept 27 28 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 169 (accept_3_3 26 28 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 169 (Polychromatic418967fa.accept_15_10_13_4_1_1210 25 28 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 28 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 169 (accept_3_3 23 28 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 28 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 169 (accept_3_3 20 28 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 169 (Polychromatic418967fa.accept_16_3_12_9_1_8250 19 28 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 169 (Polychromatic418967fa.accept_16_2_12_9_1_2568 18 28 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 169 (accept_3_3 17 28 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 169 (Polychromatic418967fa.accept_21_16_7_1_1_9430 16 28
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 169 (accept_3_3 14 28 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 169 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 28 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 28 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 169 (accept_3_3 11 28 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 169 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 28 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 169 (accept_3_3 8 28 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  169 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 28 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 169 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 28 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 169 (accept_3_3 5 28 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 169 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 28 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 169 (accept_3_3 2 28 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 169 (Polychromatic418967fa.accept_10_1_8_9_1_787 1
  28 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 169))))))))))))))))))))))))))))
  (allB_succ 27 169 (allA_succ_of_accept 26 27 169 (accept_3_3 26 27 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 169 (Polychromatic418967fa.accept_19_6_8_17_1_1524 25 27 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 169 (Polychromatic418967fa.accept_15_9_12_4_1_2023 24 27
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 169 (accept_3_3 23 27 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 22
  27 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 169
  (Polychromatic418967fa.accept_11_10_5_4_1_711 21 27 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 169 (accept_3_3 20 27 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 27 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 169 (accept_3_3 17 27 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 169
  (Polychromatic418967fa.accept_19_15_8_17_1_9429 15 27 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 169 (accept_3_3 14 27 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 169 (Polychromatic418967fa.accept_23_13_4_8_1_9428 13 27 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 169 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 27 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 169 (accept_3_3 11 27 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 169
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 27 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 169 (accept_3_3 8 27 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  169 (Polychromatic418967fa.accept_14_7_13_1_1_922 7 27 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 169 (accept_3_3 5 27 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 169
  (Polychromatic418967fa.accept_18_3_9_7_1_1839 3 27 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 169 (accept_3_3 2 27 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  169 (Polychromatic418967fa.accept_15_1_12_4_1_2022 1 27 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 169))))))))))))))))))))))))))) (allB_succ 26 169 (allA_of_3_1 26 26 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 25 169 (allA_succ_of_accept 24 25 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 25
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 169 (accept_3_3 23 25 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 169 (Polychromatic418967fa.accept_15_7_10_4_1_151
  22 25 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 169
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 25 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 25 169 (accept_3_3 20 25 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  25 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 25 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 25 169 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 25 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 169 (accept_3_3 17 25 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 169 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 25 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 169
  (Polychromatic418967fa.accept_20_15_5_9_1_3479 15 25 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 169 (accept_3_3 14 25 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 169 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 25 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 169 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 25 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 169 (accept_3_3 11 25 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 25 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 169
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 25 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 169 (accept_3_3 8 25 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  169 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 25 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 25 169 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 25 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 169 (accept_3_3 5 25 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 25 169 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 25 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 25
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 169 (accept_3_3 2 25 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 169 (Polychromatic418967fa.accept_10_1_5_9_1_157 1
  25 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 169)))))))))))))))))))))))))
  (allB_succ 24 169 (allA_succ_of_accept 23 24 169 (accept_3_3 23 24 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 24 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 169 (accept_3_3 20 24 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 169 (Polychromatic418967fa.accept_7_5_3_1_1_424 19
  24 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 169
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 24 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 24 169 (accept_3_3 17 24 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  24 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 24 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 24 169 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 24 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 169 (accept_3_3 14 24 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 24 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 169
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 24 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 24 169 (accept_3_3 11 24 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  24 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 24 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 24 169 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 24 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 169 (accept_3_3 8 24 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 169 (Polychromatic418967fa.accept_16_7_8_9_1_9427 7 24 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 169
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 24 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 169 (accept_3_3 5 24 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24
  169 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 24 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 24 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 169 (accept_3_3 2 24 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 24 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 24 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 169)))))))))))))))))))))))) (allB_succ 23 169 (allA_of_3_1 23 23
  169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 169 (allA_succ_of_accept 21 22 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 22 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 169 (accept_3_3 20 22 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 169 (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 22 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 169 (accept_3_3 17 22 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 22 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 169
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 169 (accept_3_3 14 22 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 169 (Polychromatic418967fa.accept_16_13_6_9_1_2561 13 22 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 22 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 169 (accept_3_3 11 22 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 22 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 22 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 169 (accept_3_3 8 22 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 169 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 22 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 169 (accept_3_3 5 22 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 169 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 22 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 169 (accept_3_3 2 22 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 22
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 169)))))))))))))))))))))) (allB_succ 21
  169 (allA_succ_of_accept 20 21 169 (accept_3_3 20 21 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 21 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 21 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 21 169 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 21 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 169 (accept_3_3 17 21 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 169
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 21 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 169 (accept_3_3 14 21 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 169 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 21 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 169 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 21 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 169 (accept_3_3 11 21 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 21 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 169
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 21 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 169 (accept_3_3 8 21 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  169 (Polychromatic418967fa.accept_19_7_2_17_1_9426 7 21 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 21 169 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 21 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 169 (accept_3_3 5 21 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 169
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 21 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 169 (accept_3_3 2 21 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21
  169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 21 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 21 169))))))))))))))))))))) (allB_succ 20 169 (allA_of_3_1 20 20 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 19 169 (allA_succ_of_accept 18 19 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 169 (accept_3_3 17 19 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 169 (Polychromatic418967fa.accept_18_16_1_7_1_4083
  16 19 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 169
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 19 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 19 169 (accept_3_3 14 19 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  19 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 19 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 19 169 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 19 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 169 (accept_3_3 11 19 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 169
  (Polychromatic418967fa.accept_24_9_19_1_1_9425 9 19 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 19 169 (accept_3_3 8 19 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19
  169 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 19 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 19 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 169 (accept_3_3 5 19 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 19 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 19 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 169 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 19
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 169 (accept_3_3 2 19 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 169 (Polychromatic418967fa.accept_11_1_8_4_1_717 1
  19 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 169))))))))))))))))))) (allB_succ 18
  169 (allA_succ_of_accept 17 18 169 (accept_3_3 17 18 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 18 169 (Polychromatic418967fa.accept_15_1_3_4_1_1217 16 18 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 18 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 169 (accept_3_3 14 18 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 169 (Polychromatic418967fa.accept_19_13_18_17_1_5141 13 18 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 169
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 18 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 18 169 (accept_3_3 11 18 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  18 169 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 18 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 18 169 (Polychromatic418967fa.accept_21_9_18_1_1_9424 9 18 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 169 (accept_3_3 8 18 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 169
  (Polychromatic418967fa.accept_16_6_2_9_1_5897 6 18 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 169 (accept_3_3 5 18 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18
  169 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 18 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 18 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 169 (accept_3_3 2 18 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 18 169 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 18 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 169)))))))))))))))))) (allB_succ 17 169 (allA_of_3_1 17 17 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 16 169 (allA_succ_of_accept 15 16 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 169 (accept_3_3 14 16 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 16 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 169 (Polychromatic418967fa.accept_15_12_1_4_1_2899 12 16 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 169 (accept_3_3 11 16 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 16 169
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 169 (accept_3_3 8 16 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  169 (Polychromatic418967fa.accept_19_7_16_17_1_6567 7 16 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 16 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 16 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 169 (accept_3_3 5 16 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 16 169 (Polychromatic418967fa.accept_18_4_16_7_1_1873 4 16 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 16 169 (accept_3_3 2 16 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16
  169 (Polychromatic418967fa.accept_18_1_16_7_1_2897 1 16 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 16 169)))))))))))))))) (allB_succ 15 169 (allA_succ_of_accept 14 15 169 (accept_3_3 14 15 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 169 (Polychromatic418967fa.accept_9_4_6_7_1_286 13
  15 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 169
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 15 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 15 169 (accept_3_3 11 15 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  15 169 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 15 169 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 15 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 169 (accept_3_3 8 15 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 169 (Polychromatic418967fa.accept_19_7_15_17_1_5198 7 15 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 169 (accept_3_3 5 15 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 169 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 15 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 169 (accept_3_3 2 15 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 15 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 169))))))))))))))) (allB_succ 14 169 (allA_of_3_1 14 14 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 169 (allA_succ_of_accept 12 13 169
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 13 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 169 (accept_3_3 11 13 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 13 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 169 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 13 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 169 (accept_3_3 8 13 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 169 (Polychromatic418967fa.accept_14_7_13_1_1_922 7 13 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 169
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 13 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 169 (accept_3_3 5 13 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  169 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 13 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 169 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 13 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 169 (accept_3_3 2 13 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 169 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 13 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 169))))))))))))) (allB_succ 12 169 (allA_succ_of_accept 11 12
  169 (accept_3_3 11 12 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 169
  (Polychromatic418967fa.accept_7_3_5_1_1_72 10 12 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 12 169 (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 12 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 169 (accept_3_3 8 12 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 12 169 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 12 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 169 (Polychromatic418967fa.accept_7_6_5_1_1_416 6
  12 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 169 (accept_3_3 5 12 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 169 (Polychromatic418967fa.accept_7_4_5_1_1_418 4
  12 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12 169
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 12 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 169 (accept_3_3 2 12 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12
  169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 12 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 169)))))))))))) (allB_succ 11 169 (allA_of_3_1 11 11 169 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 169 (allA_succ_of_accept 9 10 169 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 10 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 169 (accept_3_3 8 10 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 169
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 10 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 169 (accept_3_3 5 10 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  169 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 10 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 10 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 169 (accept_3_3 2 10 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 10 169 (Polychromatic418967fa.accept_16_1_10_9_1_4645 1 10 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 169)))))))))) (allB_succ 9 169 (allA_succ_of_accept 8 9 169
  (accept_3_3 8 9 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 169
  (Polychromatic418967fa.accept_19_7_9_17_1_2638 7 9 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 169 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 9 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 169 (accept_3_3 5 9 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 169 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 169 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 9
  169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 169 (accept_3_3 2 9 169
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 169 (Polychromatic418967fa.accept_19_1_9_17_1_8039 1
  9 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 169))))))))) (allB_succ 8 169
  (allA_of_3_1 8 8 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 169 (allA_succ_of_accept 6 7 169
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 169 (accept_3_3 5 7 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 169
  (Polychromatic418967fa.accept_21_4_7_1_1_6307 4 7 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 169 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 7 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 169 (accept_3_3 2 7 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 169 (Polychromatic418967fa.accept_23_1_7_8_1_9423 1 7 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 169))))))) (allB_succ 6 169 (allA_succ_of_accept 5 6 169
  (accept_3_3 5 6 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 169
  (Polychromatic418967fa.accept_9_4_6_7_1_286 4 6 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 169 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 169 (accept_3_3 2 6 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 169 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 6 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 169)))))) (allB_succ 5 169 (allA_of_3_1 5 5 169 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 169 (allA_succ_of_accept 3 4 169
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 169 (accept_3_3 2 4 169 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 169
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 4 169 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 169)))) (allB_succ 3 169 (allA_succ_of_accept 2 3 169 (accept_3_3 2 3 169 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 169 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 3 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 169))) (allB_succ 2 169 (allA_of_3_1 2 2 169 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  169)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


